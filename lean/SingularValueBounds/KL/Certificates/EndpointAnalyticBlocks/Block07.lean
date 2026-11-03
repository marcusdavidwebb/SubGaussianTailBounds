import SingularValueBounds.KL.Certificates.EndpointAnalyticLogs
import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SingularValueBounds.KL.Certificates

namespace EndpointAnalyticJoint42_18
private noncomputable def weights : IntegerLookupTree := (.branch 1403 (.leaf (66971685900000:ℤ)) (.branch 2456 (.leaf (33350651300000:ℤ)) (.leaf (5730293100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2071372960033001:ℤ)) (.branch 142 (.leaf (2535567264437977:ℤ)) (.leaf (3461960646406687:ℤ)))), (.branch 124 (.leaf (2079570466758822:ℤ)) (.branch 142 (.leaf (2551708324705765:ℤ)) (.leaf (3499804407145528:ℤ)))), (.branch 124 (.leaf (2091574292709115:ℤ)) (.branch 142 (.leaf (2590474792888880:ℤ)) (.leaf (3681232808101356:ℤ)))), (.branch 124 (.leaf (2100268401532961:ℤ)) (.branch 142 (.leaf (2608107367767168:ℤ)) (.leaf (3726148454404659:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 42 18) 8000 (endpointMeanRuns 42 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 42 18, EndpointRunConditions (endpointMeanCutoff 42 18) (endpointMeanBox 42 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 42 18 h) (endpointMeanCornerA 42 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 18, endpointJoint24Q (endpointMeanCornerK 42 18 h) (endpointMeanCornerA 42 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 42 18, endpointRunWeightQ (endpointMeanCutoff 42 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 42 18) = (188825071/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 42 18 h = (logRoundedQ ((endpointMeanCutoff 42 18:ℚ)/200)).2+(188825071/500000000000000:ℚ)+((endpointMeanRuns 42 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 42 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 42 18) r*endpointJoint24Q (endpointMeanCornerK 42 18 h) (endpointMeanCornerA 42 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 42 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 42 18 h≤endpointMeanCorner 42 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 42 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint42_18

namespace EndpointAnalyticJoint42_19
private noncomputable def weights : IntegerLookupTree := (.branch 1403 (.leaf (65193951400000:ℤ)) (.branch 2456 (.leaf (33211243000000:ℤ)) (.leaf (5712066000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2079570466758822:ℤ)) (.branch 142 (.leaf (2551708324705765:ℤ)) (.leaf (3499804407145528:ℤ)))), (.branch 124 (.leaf (2101262343372070:ℤ)) (.branch 142 (.leaf (2594606341965833:ℤ)) (.leaf (3601212570755551:ℤ)))), (.branch 124 (.leaf (2100268401532961:ℤ)) (.branch 142 (.leaf (2608107367767168:ℤ)) (.leaf (3726148454404659:ℤ)))), (.branch 124 (.leaf (2123282653203364:ℤ)) (.branch 142 (.leaf (2655006679094573:ℤ)) (.leaf (3846782029645726:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 42 19) 8000 (endpointMeanRuns 42 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 42 19, EndpointRunConditions (endpointMeanCutoff 42 19) (endpointMeanBox 42 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 42 19 h) (endpointMeanCornerA 42 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 19, endpointJoint24Q (endpointMeanCornerK 42 19 h) (endpointMeanCornerA 42 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 42 19, endpointRunWeightQ (endpointMeanCutoff 42 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 42 19) = (188425821/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 42 19 h = (logRoundedQ ((endpointMeanCutoff 42 19:ℚ)/200)).2+(188425821/500000000000000:ℚ)+((endpointMeanRuns 42 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 42 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 42 19) r*endpointJoint24Q (endpointMeanCornerK 42 19 h) (endpointMeanCornerA 42 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 42 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 42 19 h≤endpointMeanCorner 42 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 42 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint42_19

namespace EndpointAnalyticJoint42_20
private noncomputable def weights : IntegerLookupTree := (.branch 1438 (.leaf (66055692900000:ℤ)) (.branch 2456 (.leaf (29821100000000:ℤ)) (.leaf (5684960300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2101262343372070:ℤ)) (.branch 141 (.leaf (2594606341965833:ℤ)) (.leaf (3518394371009040:ℤ)))), (.branch 124 (.leaf (2123180486668043:ℤ)) (.branch 141 (.leaf (2638225538785114:ℤ)) (.leaf (3617036260686258:ℤ)))), (.branch 124 (.leaf (2123282653203364:ℤ)) (.branch 141 (.leaf (2655006679094573:ℤ)) (.leaf (3741499379021448:ℤ)))), (.branch 124 (.leaf (2146549089680037:ℤ)) (.branch 141 (.leaf (2702749339675989:ℤ)) (.leaf (3858238593090575:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 42 20) 8000 (endpointMeanRuns 42 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 42 20, EndpointRunConditions (endpointMeanCutoff 42 20) (endpointMeanBox 42 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 42 20 h) (endpointMeanCornerA 42 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 20, endpointJoint24Q (endpointMeanCornerK 42 20 h) (endpointMeanCornerA 42 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 42 20, endpointRunWeightQ (endpointMeanCutoff 42 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 42 20) = (187832091/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 42 20 h = (logRoundedQ ((endpointMeanCutoff 42 20:ℚ)/200)).2+(187832091/500000000000000:ℚ)+((endpointMeanRuns 42 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 42 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 42 20) r*endpointJoint24Q (endpointMeanCornerK 42 20 h) (endpointMeanCornerA 42 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 42 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 42 20 h≤endpointMeanCorner 42 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 42 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint42_20

namespace EndpointAnalyticJoint42_21
private noncomputable def weights : IntegerLookupTree := (.branch 1511 (.leaf (70352066900000:ℤ)) (.branch 2456 (.leaf (23913403300000:ℤ)) (.leaf (5658131300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2123180486668043:ℤ)) (.branch 139 (.leaf (2638225538785114:ℤ)) (.leaf (3455051676155288:ℤ)))), (.branch 124 (.leaf (2145327256821133:ℤ)) (.branch 139 (.leaf (2682578039266063:ℤ)) (.leaf (3545864705440390:ℤ)))), (.branch 124 (.leaf (2146549089680037:ℤ)) (.branch 139 (.leaf (2702749339675989:ℤ)) (.leaf (3655566748453007:ℤ)))), (.branch 124 (.leaf (2170070474345308:ℤ)) (.branch 139 (.leaf (2751350514722675:ℤ)) (.leaf (3761742004173464:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 42 21) 8000 (endpointMeanRuns 42 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 42 21, EndpointRunConditions (endpointMeanCutoff 42 21) (endpointMeanBox 42 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 42 21 h) (endpointMeanCornerA 42 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 21, endpointJoint24Q (endpointMeanCornerK 42 21 h) (endpointMeanCornerA 42 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 42 21, endpointRunWeightQ (endpointMeanCutoff 42 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 42 21) = (187244423/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 42 21 h = (logRoundedQ ((endpointMeanCutoff 42 21:ℚ)/200)).2+(187244423/500000000000000:ℚ)+((endpointMeanRuns 42 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 42 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 42 21) r*endpointJoint24Q (endpointMeanCornerK 42 21 h) (endpointMeanCornerA 42 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 42 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 42 21 h≤endpointMeanCorner 42 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 42 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint42_21

namespace EndpointAnalyticJoint42_22
private noncomputable def weights : IntegerLookupTree := (.branch 2105 (.leaf (109694828200000:ℤ)) (.leaf (13496293200000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 128 (.leaf (2145327256821133:ℤ)) (.leaf (2860484148806776:ℤ))), (.branch 128 (.leaf (2167705038624572:ℤ)) (.leaf (2914424279482344:ℤ))), (.branch 128 (.leaf (2170070474345308:ℤ)) (.leaf (2950840694876760:ℤ))), (.branch 128 (.leaf (2193849600862018:ℤ)) (.leaf (3010737652808432:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 42 22) 8000 (endpointMeanRuns 42 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 42 22, EndpointRunConditions (endpointMeanCutoff 42 22) (endpointMeanBox 42 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 42 22 h) (endpointMeanCornerA 42 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 22, endpointJoint24Q (endpointMeanCornerK 42 22 h) (endpointMeanCornerA 42 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 42 22, endpointRunWeightQ (endpointMeanCutoff 42 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 42 22) = (37332539/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 42 22 h = (logRoundedQ ((endpointMeanCutoff 42 22:ℚ)/200)).2+(37332539/100000000000000:ℚ)+((endpointMeanRuns 42 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 42 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 42 22) r*endpointJoint24Q (endpointMeanCornerK 42 22 h) (endpointMeanCornerA 42 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 42 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 42 22 h≤endpointMeanCorner 42 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 42 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint42_22

namespace EndpointAnalyticJoint42_23
private noncomputable def weights : IntegerLookupTree := (.branch 2456 (.leaf (123268913500000:ℤ)) (.leaf (5605281500000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2167705038624572:ℤ)) (.leaf (2727676171335361:ℤ))), (.branch 124 (.leaf (2190316241747226:ℤ)) (.leaf (2773532470170501:ℤ))), (.branch 124 (.leaf (2193849600862018:ℤ)) (.leaf (2800825642148612:ℤ))), (.branch 124 (.leaf (2217889293505300:ℤ)) (.leaf (2851190437474261:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 42 23) 8000 (endpointMeanRuns 42 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 42 23, EndpointRunConditions (endpointMeanCutoff 42 23) (endpointMeanBox 42 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 42 23 h) (endpointMeanCornerA 42 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 23, endpointJoint24Q (endpointMeanCornerK 42 23 h) (endpointMeanCornerA 42 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 42 23, endpointRunWeightQ (endpointMeanCutoff 42 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 42 23) = (186086787/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 42 23 h = (logRoundedQ ((endpointMeanCutoff 42 23:ℚ)/200)).2+(186086787/500000000000000:ℚ)+((endpointMeanRuns 42 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 42 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 42 23) r*endpointJoint24Q (endpointMeanCornerK 42 23 h) (endpointMeanCornerA 42 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 42 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 42 23 h≤endpointMeanCorner 42 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 42 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint42_23

namespace EndpointAnalyticJoint42_24
private noncomputable def weights : IntegerLookupTree := (.branch 2456 (.leaf (119627900100000:ℤ)) (.leaf (5579249800000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2190316241747226:ℤ)) (.leaf (2773532470170501:ℤ))), (.branch 124 (.leaf (2213163300993089:ℤ)) (.leaf (2820159681683969:ℤ))), (.branch 124 (.leaf (2217889293505300:ℤ)) (.leaf (2851190437474261:ℤ))), (.branch 124 (.leaf (2242192407498051:ℤ)) (.leaf (2902460898818537:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 42 24) 8000 (endpointMeanRuns 42 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 42 24, EndpointRunConditions (endpointMeanCutoff 42 24) (endpointMeanBox 42 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 42 24 h) (endpointMeanCornerA 42 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 24, endpointJoint24Q (endpointMeanCornerK 42 24 h) (endpointMeanCornerA 42 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 42 24, endpointRunWeightQ (endpointMeanCutoff 42 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 42 24) = (371033169/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 42 24 h = (logRoundedQ ((endpointMeanCutoff 42 24:ℚ)/200)).2+(371033169/1000000000000000:ℚ)+((endpointMeanRuns 42 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 42 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 42 24) r*endpointJoint24Q (endpointMeanCornerK 42 24 h) (endpointMeanCornerA 42 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 42 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 42 24 h≤endpointMeanCorner 42 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 42 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint42_24

namespace EndpointAnalyticJoint42_25
private noncomputable def weights : IntegerLookupTree := (.branch 2456 (.leaf (115710579500000:ℤ)) (.leaf (5550625100000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2213163300993089:ℤ)) (.leaf (2820159681683969:ℤ))), (.branch 124 (.leaf (2236248676563426:ℤ)) (.leaf (2867570766066029:ℤ))), (.branch 124 (.leaf (2242192407498051:ℤ)) (.leaf (2902460898818537:ℤ))), (.branch 124 (.leaf (2266761829350022:ℤ)) (.leaf (2954653311980519:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 42 25) 8000 (endpointMeanRuns 42 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 42 25, EndpointRunConditions (endpointMeanCutoff 42 25) (endpointMeanBox 42 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 42 25 h) (endpointMeanCornerA 42 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 25, endpointJoint24Q (endpointMeanCornerK 42 25 h) (endpointMeanCornerA 42 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 42 25, endpointRunWeightQ (endpointMeanCutoff 42 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 42 25) = (369779163/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 42 25 h = (logRoundedQ ((endpointMeanCutoff 42 25:ℚ)/200)).2+(369779163/1000000000000000:ℚ)+((endpointMeanRuns 42 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 42 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 42 25) r*endpointJoint24Q (endpointMeanCornerK 42 25 h) (endpointMeanCornerA 42 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 42 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 42 25 h≤endpointMeanCorner 42 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 42 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint42_25

namespace EndpointAnalyticJoint42_26
private noncomputable def weights : IntegerLookupTree := (.branch 2456 (.leaf (112296658200000:ℤ)) (.leaf (5525126800000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2236248676563426:ℤ)) (.leaf (2867570766066029:ℤ))), (.branch 124 (.leaf (2259574854321739:ℤ)) (.leaf (2915778901387038:ℤ))), (.branch 124 (.leaf (2266761829350022:ℤ)) (.leaf (2954653311980519:ℤ))), (.branch 124 (.leaf (2291600477200676:ℤ)) (.leaf (3007784255612552:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 42 26) 8000 (endpointMeanRuns 42 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 42 26, EndpointRunConditions (endpointMeanCutoff 42 26) (endpointMeanBox 42 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 42 26 h) (endpointMeanCornerA 42 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 26, endpointJoint24Q (endpointMeanCornerK 42 26 h) (endpointMeanCornerA 42 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 42 26, endpointRunWeightQ (endpointMeanCutoff 42 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 42 26) = (9216553/25000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 42 26 h = (logRoundedQ ((endpointMeanCutoff 42 26:ℚ)/200)).2+(9216553/25000000000000:ℚ)+((endpointMeanRuns 42 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 42 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 42 26) r*endpointJoint24Q (endpointMeanCornerK 42 26 h) (endpointMeanCornerA 42 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 42 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 42 26 h≤endpointMeanCorner 42 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 42 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint42_26

namespace EndpointAnalyticJoint42_27
private noncomputable def weights : IntegerLookupTree := (.branch 2456 (.leaf (108985090600000:ℤ)) (.leaf (5499873500000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2259574854321739:ℤ)) (.leaf (2915778901387038:ℤ))), (.branch 124 (.leaf (2283144346061416:ℤ)) (.leaf (2964797487260351:ℤ))), (.branch 124 (.leaf (2291600477200676:ℤ)) (.leaf (3007784255612552:ℤ))), (.branch 124 (.leaf (2316711301165755:ℤ)) (.leaf (3061870606486368:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 42 27) 8000 (endpointMeanRuns 42 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 42 27, EndpointRunConditions (endpointMeanCutoff 42 27) (endpointMeanBox 42 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 42 27 h) (endpointMeanCornerA 42 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 27, endpointJoint24Q (endpointMeanCornerK 42 27 h) (endpointMeanCornerA 42 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 42 27, endpointRunWeightQ (endpointMeanCutoff 42 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 42 27) = (91888953/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 42 27 h = (logRoundedQ ((endpointMeanCutoff 42 27:ℚ)/200)).2+(91888953/250000000000000:ℚ)+((endpointMeanRuns 42 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 42 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 42 27) r*endpointJoint24Q (endpointMeanCornerK 42 27 h) (endpointMeanCornerA 42 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 42 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 42 27 h≤endpointMeanCorner 42 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 42 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint42_27

namespace EndpointAnalyticJoint42_28
private noncomputable def weights : IntegerLookupTree := (.leaf (191367106700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2283144346061416:ℤ)), (.leaf (2306959689776218:ℤ)), (.leaf (2316711301165755:ℤ)), (.leaf (2342097283687694:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 42 28) 8000 (endpointMeanRuns 42 28) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 42 28, EndpointRunConditions (endpointMeanCutoff 42 28) (endpointMeanBox 42 28).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 28, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 42 28 h) (endpointMeanCornerA 42 28 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 28, endpointJoint24Q (endpointMeanCornerK 42 28 h) (endpointMeanCornerA 42 28 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 42 28, endpointRunWeightQ (endpointMeanCutoff 42 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 42 28) = (73292007/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 42 28 h = (logRoundedQ ((endpointMeanCutoff 42 28:ℚ)/200)).2+(73292007/200000000000000:ℚ)+((endpointMeanRuns 42 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 42 28).map (fun r => endpointRunWeightQ (endpointMeanCutoff 42 28) r*endpointJoint24Q (endpointMeanCornerK 42 28 h) (endpointMeanCornerA 42 28 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 42 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 42 28 h≤endpointMeanCorner 42 28 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 42 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint42_28

namespace EndpointAnalyticJoint42_29
private noncomputable def weights : IntegerLookupTree := (.leaf (187563688700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2306959689776218:ℤ)), (.leaf (2321367970662042:ℤ)), (.leaf (2342097283687694:ℤ)), (.leaf (2357462202229238:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 42 29) 8000 (endpointMeanRuns 42 29) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 42 29, EndpointRunConditions (endpointMeanCutoff 42 29) (endpointMeanBox 42 29).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 29, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 42 29 h) (endpointMeanCornerA 42 29 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 29, endpointJoint24Q (endpointMeanCornerK 42 29 h) (endpointMeanCornerA 42 29 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 42 29, endpointRunWeightQ (endpointMeanCutoff 42 29) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 42 29) = (365614917/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 42 29 h = (logRoundedQ ((endpointMeanCutoff 42 29:ℚ)/200)).2+(365614917/1000000000000000:ℚ)+((endpointMeanRuns 42 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 42 29).map (fun r => endpointRunWeightQ (endpointMeanCutoff 42 29) r*endpointJoint24Q (endpointMeanCornerK 42 29 h) (endpointMeanCornerA 42 29 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 42 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 42 29 h≤endpointMeanCorner 42 29 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 42 29 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint42_29

namespace EndpointAnalyticJoint42_30
private noncomputable def weights : IntegerLookupTree := (.branch 2456 (.leaf (101976547500000:ℤ)) (.leaf (5444609100000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2321367970662042:ℤ)) (.leaf (3044947055152078:ℤ))), (.branch 124 (.leaf (2331023449933551:ℤ)) (.leaf (3065320739241667:ℤ))), (.branch 124 (.leaf (2357462202229238:ℤ)) (.leaf (3150439012356717:ℤ))), (.branch 124 (.leaf (2367761439889833:ℤ)) (.leaf (3172978559904568:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 42 30) 8000 (endpointMeanRuns 42 30) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 42 30, EndpointRunConditions (endpointMeanCutoff 42 30) (endpointMeanBox 42 30).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 30, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 42 30 h) (endpointMeanCornerA 42 30 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 30, endpointJoint24Q (endpointMeanCornerK 42 30 h) (endpointMeanCornerA 42 30 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 42 30, endpointRunWeightQ (endpointMeanCutoff 42 30) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 42 30) = (365134763/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 42 30 h = (logRoundedQ ((endpointMeanCutoff 42 30:ℚ)/200)).2+(365134763/1000000000000000:ℚ)+((endpointMeanRuns 42 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 42 30).map (fun r => endpointRunWeightQ (endpointMeanCutoff 42 30) r*endpointJoint24Q (endpointMeanCornerK 42 30 h) (endpointMeanCornerA 42 30 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 42 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 42 30 h≤endpointMeanCorner 42 30 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 42 30 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint42_30

namespace EndpointAnalyticJoint42_31
private noncomputable def weights : IntegerLookupTree := (.branch 2105 (.leaf (85028223200000:ℤ)) (.leaf (12969412400000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 128 (.leaf (2331023449933551:ℤ)) (.leaf (3321585161396946:ℤ))), (.branch 128 (.leaf (2355338217750656:ℤ)) (.leaf (3384220270817320:ℤ))), (.branch 128 (.leaf (2367761439889833:ℤ)) (.leaf (3465476535450314:ℤ))), (.branch 128 (.leaf (2393706817934531:ℤ)) (.leaf (3535819710064056:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 42 31) 8000 (endpointMeanRuns 42 31) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 42 31, EndpointRunConditions (endpointMeanCutoff 42 31) (endpointMeanBox 42 31).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 31, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 42 31 h) (endpointMeanCornerA 42 31 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 31, endpointJoint24Q (endpointMeanCornerK 42 31 h) (endpointMeanCornerA 42 31 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 42 31, endpointRunWeightQ (endpointMeanCutoff 42 31) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 42 31) = (91074821/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 42 31 h = (logRoundedQ ((endpointMeanCutoff 42 31:ℚ)/200)).2+(91074821/250000000000000:ℚ)+((endpointMeanRuns 42 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 42 31).map (fun r => endpointRunWeightQ (endpointMeanCutoff 42 31) r*endpointJoint24Q (endpointMeanCornerK 42 31 h) (endpointMeanCornerA 42 31 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 42 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 42 31 h≤endpointMeanCorner 42 31 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 42 31 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint42_31

namespace EndpointAnalyticJoint42_32
private noncomputable def weights : IntegerLookupTree := (.branch 2456 (.leaf (96699956500000:ℤ)) (.leaf (5401219400000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2355338217750656:ℤ)) (.leaf (3116853346125643:ℤ))), (.branch 124 (.leaf (2379906611473592:ℤ)) (.leaf (3169252292880114:ℤ))), (.branch 124 (.leaf (2393706817934531:ℤ)) (.leaf (3230035455320472:ℤ))), (.branch 124 (.leaf (2419936499385193:ℤ)) (.leaf (3288118354931820:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 42 32) 8000 (endpointMeanRuns 42 32) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 42 32, EndpointRunConditions (endpointMeanCutoff 42 32) (endpointMeanBox 42 32).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 32, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 42 32 h) (endpointMeanCornerA 42 32 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 42 32, endpointJoint24Q (endpointMeanCornerK 42 32 h) (endpointMeanCornerA 42 32 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 42 32, endpointRunWeightQ (endpointMeanCutoff 42 32) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 42 32) = (36323393/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 42 32 h = (logRoundedQ ((endpointMeanCutoff 42 32:ℚ)/200)).2+(36323393/100000000000000:ℚ)+((endpointMeanRuns 42 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 42 32).map (fun r => endpointRunWeightQ (endpointMeanCutoff 42 32) r*endpointJoint24Q (endpointMeanCornerK 42 32 h) (endpointMeanCornerA 42 32 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 42 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 42 32 h≤endpointMeanCorner 42 32 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 42 32 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint42_32

namespace EndpointAnalyticJoint43_19
private noncomputable def weights : IntegerLookupTree := (.branch 1527 (.leaf (71486488800000:ℤ)) (.branch 2417 (.leaf (22518964000000:ℤ)) (.leaf (6222804300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2112548025604330:ℤ)) (.branch 138 (.leaf (2633090842069462:ℤ)) (.leaf (3422678376947311:ℤ)))), (.branch 124 (.leaf (2123282653203364:ℤ)) (.branch 138 (.leaf (2655006679094573:ℤ)) (.leaf (3466999556525967:ℤ)))), (.branch 124 (.leaf (2136214579146610:ℤ)) (.branch 138 (.leaf (2702216627180039:ℤ)) (.leaf (3643262081225875:ℤ)))), (.branch 124 (.leaf (2147639006104329:ℤ)) (.branch 138 (.leaf (2726389338441273:ℤ)) (.leaf (3695931143958891:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 43 19) 8000 (endpointMeanRuns 43 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 43 19, EndpointRunConditions (endpointMeanCutoff 43 19) (endpointMeanBox 43 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 43 19 h) (endpointMeanCornerA 43 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 19, endpointJoint24Q (endpointMeanCornerK 43 19 h) (endpointMeanCornerA 43 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 43 19, endpointRunWeightQ (endpointMeanCutoff 43 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 43 19) = (37384103/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 43 19 h = (logRoundedQ ((endpointMeanCutoff 43 19:ℚ)/200)).2+(37384103/100000000000000:ℚ)+((endpointMeanRuns 43 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 43 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 43 19) r*endpointJoint24Q (endpointMeanCornerK 43 19 h) (endpointMeanCornerA 43 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 43 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 43 19 h≤endpointMeanCorner 43 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 43 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint43_19

namespace EndpointAnalyticJoint43_20
private noncomputable def weights : IntegerLookupTree := (.branch 1527 (.leaf (69427736600000:ℤ)) (.branch 2417 (.leaf (22414677100000:ℤ)) (.leaf (6199979400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2123282653203364:ℤ)) (.branch 138 (.leaf (2655006679094573:ℤ)) (.leaf (3466999556525967:ℤ)))), (.branch 124 (.leaf (2146549089680037:ℤ)) (.branch 138 (.leaf (2702749339675989:ℤ)) (.leaf (3564251292673661:ℤ)))), (.branch 124 (.leaf (2147639006104329:ℤ)) (.branch 138 (.leaf (2726389338441273:ℤ)) (.leaf (3695931143958891:ℤ)))), (.branch 124 (.leaf (2172410883694733:ℤ)) (.branch 138 (.leaf (2779099778320986:ℤ)) (.leaf (3811771912445314:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 43 20) 8000 (endpointMeanRuns 43 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 43 20, EndpointRunConditions (endpointMeanCutoff 43 20) (endpointMeanBox 43 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 43 20 h) (endpointMeanCornerA 43 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 20, endpointJoint24Q (endpointMeanCornerK 43 20 h) (endpointMeanCornerA 43 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 43 20, endpointRunWeightQ (endpointMeanCutoff 43 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 43 20) = (372940169/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 43 20 h = (logRoundedQ ((endpointMeanCutoff 43 20:ℚ)/200)).2+(372940169/1000000000000000:ℚ)+((endpointMeanRuns 43 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 43 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 43 20) r*endpointJoint24Q (endpointMeanCornerK 43 20 h) (endpointMeanCornerA 43 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 43 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 43 20 h≤endpointMeanCorner 43 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 43 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint43_20

namespace EndpointAnalyticJoint43_21
private noncomputable def weights : IntegerLookupTree := (.branch 1568 (.leaf (70356101300000:ℤ)) (.branch 2417 (.leaf (19677998900000:ℤ)) (.leaf (6170893300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2146549089680037:ℤ)) (.branch 137 (.leaf (2702749339675989:ℤ)) (.leaf (3478677419392369:ℤ)))), (.branch 124 (.leaf (2170070474345308:ℤ)) (.branch 137 (.leaf (2751350514722675:ℤ)) (.leaf (3572971173224553:ℤ)))), (.branch 124 (.leaf (2172410883694733:ℤ)) (.branch 137 (.leaf (2779099778320986:ℤ)) (.leaf (3702562567235053:ℤ)))), (.branch 124 (.leaf (2197468491762935:ℤ)) (.branch 137 (.leaf (2832829291461123:ℤ)) (.leaf (3814237019101608:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 43 21) 8000 (endpointMeanRuns 43 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 43 21, EndpointRunConditions (endpointMeanCutoff 43 21) (endpointMeanBox 43 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 43 21 h) (endpointMeanCornerA 43 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 21, endpointJoint24Q (endpointMeanCornerK 43 21 h) (endpointMeanCornerA 43 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 43 21, endpointRunWeightQ (endpointMeanCutoff 43 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 43 21) = (185896091/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 43 21 h = (logRoundedQ ((endpointMeanCutoff 43 21:ℚ)/200)).2+(185896091/500000000000000:ℚ)+((endpointMeanRuns 43 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 43 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 43 21) r*endpointJoint24Q (endpointMeanCornerK 43 21 h) (endpointMeanCornerA 43 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 43 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 43 21 h≤endpointMeanCorner 43 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 43 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint43_21

namespace EndpointAnalyticJoint43_22
private noncomputable def weights : IntegerLookupTree := (.branch 2417 (.leaf (117842122100000:ℤ)) (.leaf (6138911900000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2170070474345308:ℤ)) (.leaf (2751350514722675:ℤ))), (.branch 124 (.leaf (2193849600862018:ℤ)) (.leaf (2800825642148612:ℤ))), (.branch 124 (.leaf (2197468491762935:ℤ)) (.leaf (2832829291461123:ℤ))), (.branch 124 (.leaf (2222815126058545:ℤ)) (.leaf (2887597580036675:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 43 22) 8000 (endpointMeanRuns 43 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 43 22, EndpointRunConditions (endpointMeanCutoff 43 22) (endpointMeanBox 43 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 43 22 h) (endpointMeanCornerA 43 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 22, endpointJoint24Q (endpointMeanCornerK 43 22 h) (endpointMeanCornerA 43 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 43 22, endpointRunWeightQ (endpointMeanCutoff 43 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 43 22) = (185264963/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 43 22 h = (logRoundedQ ((endpointMeanCutoff 43 22:ℚ)/200)).2+(185264963/500000000000000:ℚ)+((endpointMeanRuns 43 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 43 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 43 22) r*endpointJoint24Q (endpointMeanCornerK 43 22 h) (endpointMeanCornerA 43 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 43 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 43 22 h≤endpointMeanCorner 43 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 43 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint43_22

namespace EndpointAnalyticJoint43_23
private noncomputable def weights : IntegerLookupTree := (.branch 2072 (.leaf (98073490000000:ℤ)) (.leaf (14391649700000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 128 (.leaf (2193849600862018:ℤ)) (.leaf (3010737652808432:ℤ))), (.branch 128 (.leaf (2217889293505300:ℤ)) (.leaf (3071850415299021:ℤ))), (.branch 128 (.leaf (2222815126058545:ℤ)) (.leaf (3128048656697651:ℤ))), (.branch 128 (.leaf (2248454120345904:ℤ)) (.leaf (3196851142075722:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 43 23) 8000 (endpointMeanRuns 43 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 43 23, EndpointRunConditions (endpointMeanCutoff 43 23) (endpointMeanBox 43 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 43 23 h) (endpointMeanCornerA 43 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 23, endpointJoint24Q (endpointMeanCornerK 43 23 h) (endpointMeanCornerA 43 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 43 23, endpointRunWeightQ (endpointMeanCutoff 43 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 43 23) = (36940561/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 43 23 h = (logRoundedQ ((endpointMeanCutoff 43 23:ℚ)/200)).2+(36940561/100000000000000:ℚ)+((endpointMeanRuns 43 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 43 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 43 23) r*endpointJoint24Q (endpointMeanCornerK 43 23 h) (endpointMeanCornerA 43 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 43 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 43 23 h≤endpointMeanCorner 43 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 43 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint43_23

namespace EndpointAnalyticJoint43_24
private noncomputable def weights : IntegerLookupTree := (.branch 2072 (.leaf (95032195500000:ℤ)) (.leaf (14320656500000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 128 (.leaf (2217889293505300:ℤ)) (.leaf (3071850415299021:ℤ))), (.branch 128 (.leaf (2242192407498051:ℤ)) (.leaf (3134203661076403:ℤ))), (.branch 128 (.leaf (2248454120345904:ℤ)) (.leaf (3196851142075722:ℤ))), (.branch 128 (.leaf (2274388846842551:ℤ)) (.leaf (3267166961328590:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 43 24) 8000 (endpointMeanRuns 43 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 43 24, EndpointRunConditions (endpointMeanCutoff 43 24) (endpointMeanBox 43 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 43 24 h) (endpointMeanCornerA 43 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 24, endpointJoint24Q (endpointMeanCornerK 43 24 h) (endpointMeanCornerA 43 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 43 24, endpointRunWeightQ (endpointMeanCutoff 43 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 43 24) = (46036521/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 43 24 h = (logRoundedQ ((endpointMeanCutoff 43 24:ℚ)/200)).2+(46036521/125000000000000:ℚ)+((endpointMeanRuns 43 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 43 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 43 24) r*endpointJoint24Q (endpointMeanCornerK 43 24 h) (endpointMeanCornerA 43 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 43 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 43 24 h≤endpointMeanCorner 43 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 43 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint43_24

namespace EndpointAnalyticJoint43_25
private noncomputable def weights : IntegerLookupTree := (.branch 2417 (.leaf (107703504600000:ℤ)) (.leaf (6054273900000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2242192407498051:ℤ)) (.leaf (2902460898818537:ℤ))), (.branch 124 (.leaf (2266761829350022:ℤ)) (.leaf (2954653311980519:ℤ))), (.branch 124 (.leaf (2274388846842551:ℤ)) (.leaf (3000331204110727:ℤ))), (.branch 124 (.leaf (2300622716662769:ℤ)) (.leaf (3058337878111262:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 43 25) 8000 (endpointMeanRuns 43 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 43 25, EndpointRunConditions (endpointMeanCutoff 43 25) (endpointMeanBox 43 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 43 25 h) (endpointMeanCornerA 43 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 25, endpointJoint24Q (endpointMeanCornerK 43 25 h) (endpointMeanCornerA 43 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 43 25, endpointRunWeightQ (endpointMeanCutoff 43 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 43 25) = (367189393/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 43 25 h = (logRoundedQ ((endpointMeanCutoff 43 25:ℚ)/200)).2+(367189393/1000000000000000:ℚ)+((endpointMeanRuns 43 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 43 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 43 25) r*endpointJoint24Q (endpointMeanCornerK 43 25 h) (endpointMeanCornerA 43 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 43 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 43 25 h≤endpointMeanCorner 43 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 43 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint43_25

namespace EndpointAnalyticJoint43_26
private noncomputable def weights : IntegerLookupTree := (.branch 2417 (.leaf (104524424700000:ℤ)) (.leaf (6026598300000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2266761829350022:ℤ)) (.leaf (2954653311980519:ℤ))), (.branch 124 (.leaf (2291600477200676:ℤ)) (.leaf (3007784255612552:ℤ))), (.branch 124 (.leaf (2300622716662769:ℤ)) (.leaf (3058337878111262:ℤ))), (.branch 124 (.leaf (2327159180266233:ℤ)) (.leaf (3117466019709780:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 43 26) 8000 (endpointMeanRuns 43 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 43 26, EndpointRunConditions (endpointMeanCutoff 43 26) (endpointMeanBox 43 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 43 26 h) (endpointMeanCornerA 43 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 26, endpointJoint24Q (endpointMeanCornerK 43 26 h) (endpointMeanCornerA 43 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 43 26, endpointRunWeightQ (endpointMeanCutoff 43 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 43 26) = (366097081/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 43 26 h = (logRoundedQ ((endpointMeanCutoff 43 26:ℚ)/200)).2+(366097081/1000000000000000:ℚ)+((endpointMeanRuns 43 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 43 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 43 26) r*endpointJoint24Q (endpointMeanCornerK 43 26 h) (endpointMeanCornerA 43 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 43 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 43 26 h≤endpointMeanCorner 43 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 43 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint43_26

namespace EndpointAnalyticJoint43_27
private noncomputable def weights : IntegerLookupTree := (.branch 2417 (.leaf (101440390600000:ℤ)) (.leaf (5999182900000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2291600477200676:ℤ)) (.leaf (3007784255612552:ℤ))), (.branch 124 (.leaf (2316711301165755:ℤ)) (.leaf (3061870606486368:ℤ))), (.branch 124 (.leaf (2327159180266233:ℤ)) (.leaf (3117466019709780:ℤ))), (.branch 124 (.leaf (2354001727911849:ℤ)) (.leaf (3177737310714349:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 43 27) 8000 (endpointMeanRuns 43 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 43 27, EndpointRunConditions (endpointMeanCutoff 43 27) (endpointMeanBox 43 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 43 27 h) (endpointMeanCornerA 43 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 27, endpointJoint24Q (endpointMeanCornerK 43 27 h) (endpointMeanCornerA 43 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 43 27, endpointRunWeightQ (endpointMeanCutoff 43 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 43 27) = (365015037/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 43 27 h = (logRoundedQ ((endpointMeanCutoff 43 27:ℚ)/200)).2+(365015037/1000000000000000:ℚ)+((endpointMeanRuns 43 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 43 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 43 27) r*endpointJoint24Q (endpointMeanCornerK 43 27 h) (endpointMeanCornerA 43 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 43 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 43 27 h≤endpointMeanCorner 43 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 43 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint43_27

namespace EndpointAnalyticJoint43_28
private noncomputable def weights : IntegerLookupTree := (.leaf (179674857800000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2316711301165755:ℤ)), (.leaf (2342097283687694:ℤ)), (.leaf (2354001727911849:ℤ)), (.leaf (2381153890116803:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 43 28) 8000 (endpointMeanRuns 43 28) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 43 28, EndpointRunConditions (endpointMeanCutoff 43 28) (endpointMeanBox 43 28).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 28, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 43 28 h) (endpointMeanCornerA 43 28 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 28, endpointJoint24Q (endpointMeanCornerK 43 28 h) (endpointMeanCornerA 43 28 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 43 28, endpointRunWeightQ (endpointMeanCutoff 43 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 43 28) = (5684759/15625000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 43 28 h = (logRoundedQ ((endpointMeanCutoff 43 28:ℚ)/200)).2+(5684759/15625000000000:ℚ)+((endpointMeanRuns 43 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 43 28).map (fun r => endpointRunWeightQ (endpointMeanCutoff 43 28) r*endpointJoint24Q (endpointMeanCornerK 43 28 h) (endpointMeanCornerA 43 28 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 43 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 43 28 h≤endpointMeanCorner 43 28 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 43 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint43_28

namespace EndpointAnalyticJoint43_29
private noncomputable def weights : IntegerLookupTree := (.leaf (176111716800000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2342097283687694:ℤ)), (.leaf (2357462202229238:ℤ)), (.leaf (2381153890116803:ℤ)), (.leaf (2397595286355932:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 43 29) 8000 (endpointMeanRuns 43 29) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 43 29, EndpointRunConditions (endpointMeanCutoff 43 29) (endpointMeanBox 43 29).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 29, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 43 29 h) (endpointMeanCornerA 43 29 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 29, endpointJoint24Q (endpointMeanCornerK 43 29 h) (endpointMeanCornerA 43 29 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 43 29, endpointRunWeightQ (endpointMeanCutoff 43 29) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 43 29) = (181499259/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 43 29 h = (logRoundedQ ((endpointMeanCutoff 43 29:ℚ)/200)).2+(181499259/500000000000000:ℚ)+((endpointMeanRuns 43 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 43 29).map (fun r => endpointRunWeightQ (endpointMeanCutoff 43 29) r*endpointJoint24Q (endpointMeanCornerK 43 29 h) (endpointMeanCornerA 43 29 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 43 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 43 29 h≤endpointMeanCorner 43 29 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 43 29 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint43_29

namespace EndpointAnalyticJoint43_30
private noncomputable def weights : IntegerLookupTree := (.branch 2417 (.leaf (94283559500000:ℤ)) (.leaf (5933232700000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2357462202229238:ℤ)) (.leaf (3150439012356717:ℤ))), (.branch 124 (.leaf (2367761439889833:ℤ)) (.leaf (3172978559904568:ℤ))), (.branch 124 (.leaf (2397595286355932:ℤ)) (.leaf (3276604450891709:ℤ))), (.branch 124 (.leaf (2408619238120926:ℤ)) (.leaf (3301798172196168:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 43 30) 8000 (endpointMeanRuns 43 30) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 43 30, EndpointRunConditions (endpointMeanCutoff 43 30) (endpointMeanBox 43 30).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 30, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 43 30 h) (endpointMeanCornerA 43 30 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 30, endpointJoint24Q (endpointMeanCornerK 43 30 h) (endpointMeanCornerA 43 30 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 43 30, endpointRunWeightQ (endpointMeanCutoff 43 30) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 43 30) = (90603021/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 43 30 h = (logRoundedQ ((endpointMeanCutoff 43 30:ℚ)/200)).2+(90603021/250000000000000:ℚ)+((endpointMeanRuns 43 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 43 30).map (fun r => endpointRunWeightQ (endpointMeanCutoff 43 30) r*endpointJoint24Q (endpointMeanCornerK 43 30 h) (endpointMeanCornerA 43 30 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 43 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 43 30 h≤endpointMeanCorner 43 30 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 43 30 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint43_30

namespace EndpointAnalyticJoint43_31
private noncomputable def weights : IntegerLookupTree := (.branch 2417 (.leaf (92421801400000:ℤ)) (.leaf (5915502100000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2367761439889833:ℤ)) (.leaf (3172978559904568:ℤ))), (.branch 124 (.leaf (2393706817934531:ℤ)) (.leaf (3230035455320472:ℤ))), (.branch 124 (.leaf (2408619238120926:ℤ)) (.leaf (3301798172196168:ℤ))), (.branch 124 (.leaf (2436401384356411:ℤ)) (.leaf (3365633234781175:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 43 31) 8000 (endpointMeanRuns 43 31) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 43 31, EndpointRunConditions (endpointMeanCutoff 43 31) (endpointMeanBox 43 31).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 31, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 43 31 h) (endpointMeanCornerA 43 31 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 31, endpointJoint24Q (endpointMeanCornerK 43 31 h) (endpointMeanCornerA 43 31 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 43 31, endpointRunWeightQ (endpointMeanCutoff 43 31) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 43 31) = (72342457/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 43 31 h = (logRoundedQ ((endpointMeanCutoff 43 31:ℚ)/200)).2+(72342457/200000000000000:ℚ)+((endpointMeanRuns 43 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 43 31).map (fun r => endpointRunWeightQ (endpointMeanCutoff 43 31) r*endpointJoint24Q (endpointMeanCornerK 43 31 h) (endpointMeanCornerA 43 31 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 43 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 43 31 h≤endpointMeanCorner 43 31 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 43 31 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint43_31

namespace EndpointAnalyticJoint43_32
private noncomputable def weights : IntegerLookupTree := (.leaf (166328405000000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2393706817934531:ℤ)), (.leaf (2419936499385193:ℤ)), (.leaf (2436401384356411:ℤ)), (.leaf (2464503982922937:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 43 32) 8000 (endpointMeanRuns 43 32) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 43 32, EndpointRunConditions (endpointMeanCutoff 43 32) (endpointMeanBox 43 32).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 32, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 43 32 h) (endpointMeanCornerA 43 32 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 32, endpointJoint24Q (endpointMeanCornerK 43 32 h) (endpointMeanCornerA 43 32 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 43 32, endpointRunWeightQ (endpointMeanCutoff 43 32) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 43 32) = (360670499/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 43 32 h = (logRoundedQ ((endpointMeanCutoff 43 32:ℚ)/200)).2+(360670499/1000000000000000:ℚ)+((endpointMeanRuns 43 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 43 32).map (fun r => endpointRunWeightQ (endpointMeanCutoff 43 32) r*endpointJoint24Q (endpointMeanCornerK 43 32 h) (endpointMeanCornerA 43 32 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 43 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 43 32 h≤endpointMeanCorner 43 32 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 43 32 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint43_32

namespace EndpointAnalyticJoint43_33
private noncomputable def weights : IntegerLookupTree := (.leaf (162110793300000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2419936499385193:ℤ)), (.leaf (2446453599572292:ℤ)), (.leaf (2464503982922937:ℤ)), (.leaf (2492930730068290:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 43 33) 8000 (endpointMeanRuns 43 33) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 43 33, EndpointRunConditions (endpointMeanCutoff 43 33) (endpointMeanBox 43 33).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 33, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 43 33 h) (endpointMeanCornerA 43 33 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 43 33, endpointJoint24Q (endpointMeanCornerK 43 33 h) (endpointMeanCornerA 43 33 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 43 33, endpointRunWeightQ (endpointMeanCutoff 43 33) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 43 33) = (44954757/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 43 33 h = (logRoundedQ ((endpointMeanCutoff 43 33:ℚ)/200)).2+(44954757/125000000000000:ℚ)+((endpointMeanRuns 43 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 43 33).map (fun r => endpointRunWeightQ (endpointMeanCutoff 43 33) r*endpointJoint24Q (endpointMeanCornerK 43 33 h) (endpointMeanCornerA 43 33 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 43 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 43 33 h≤endpointMeanCorner 43 33 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 43 33 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint43_33

namespace EndpointAnalyticJoint44_20
private noncomputable def weights : IntegerLookupTree := (.branch 1970 (.leaf (95061929500000:ℤ)) (.leaf (18528990700000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 129 (.leaf (2159494055078763:ℤ)) (.leaf (3020438089920189:ℤ))), (.branch 129 (.leaf (2172410883694733:ℤ)) (.leaf (3055953867061036:ℤ))), (.branch 129 (.leaf (2187444777420636:ℤ)) (.leaf (3155429021095938:ℤ))), (.branch 129 (.leaf (2201247439911795:ℤ)) (.leaf (3196078224644949:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 44 20) 8000 (endpointMeanRuns 44 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 44 20, EndpointRunConditions (endpointMeanCutoff 44 20) (endpointMeanBox 44 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 44 20 h) (endpointMeanCornerA 44 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 20, endpointJoint24Q (endpointMeanCornerK 44 20 h) (endpointMeanCornerA 44 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 44 20, endpointRunWeightQ (endpointMeanCutoff 44 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 44 20) = (369903951/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 44 20 h = (logRoundedQ ((endpointMeanCutoff 44 20:ℚ)/200)).2+(369903951/1000000000000000:ℚ)+((endpointMeanRuns 44 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 44 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 44 20) r*endpointJoint24Q (endpointMeanCornerK 44 20 h) (endpointMeanCornerA 44 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 44 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 44 20 h≤endpointMeanCorner 44 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 44 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint44_20

namespace EndpointAnalyticJoint44_21
private noncomputable def weights : IntegerLookupTree := (.branch 1680 (.leaf (73925222400000:ℤ)) (.branch 2380 (.leaf (13467973200000:ℤ)) (.leaf (6692087600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2172410883694733:ℤ)) (.branch 134 (.leaf (2779099778320986:ℤ)) (.leaf (3419911821586689:ℤ)))), (.branch 124 (.leaf (2197468491762935:ℤ)) (.branch 134 (.leaf (2832829291461123:ℤ)) (.leaf (3512271888748937:ℤ)))), (.branch 124 (.leaf (2201247439911795:ℤ)) (.branch 134 (.leaf (2871369857729022:ℤ)) (.leaf (3646950823234348:ℤ)))), (.branch 124 (.leaf (2228036287890346:ℤ)) (.branch 134 (.leaf (2931439111352456:ℤ)) (.leaf (3756924021352409:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 44 21) 8000 (endpointMeanRuns 44 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 44 21, EndpointRunConditions (endpointMeanCutoff 44 21) (endpointMeanBox 44 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 44 21 h) (endpointMeanCornerA 44 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 21, endpointJoint24Q (endpointMeanCornerK 44 21 h) (endpointMeanCornerA 44 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 44 21, endpointRunWeightQ (endpointMeanCutoff 44 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 44 21) = (23064579/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 44 21 h = (logRoundedQ ((endpointMeanCutoff 44 21:ℚ)/200)).2+(23064579/62500000000000:ℚ)+((endpointMeanRuns 44 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 44 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 44 21) r*endpointJoint24Q (endpointMeanCornerK 44 21 h) (endpointMeanCornerA 44 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 44 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 44 21 h≤endpointMeanCorner 44 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 44 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint44_21

namespace EndpointAnalyticJoint44_22
private noncomputable def weights : IntegerLookupTree := (.branch 2380 (.leaf (109664856200000:ℤ)) (.leaf (6661041800000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2197468491762935:ℤ)) (.leaf (2832829291461123:ℤ))), (.branch 124 (.leaf (2222815126058545:ℤ)) (.leaf (2887597580036675:ℤ))), (.branch 124 (.leaf (2228036287890346:ℤ)) (.leaf (2931439111352456:ℤ))), (.branch 124 (.leaf (2255151152091791:ℤ)) (.leaf (2992765017866204:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 44 22) 8000 (endpointMeanRuns 44 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 44 22, EndpointRunConditions (endpointMeanCutoff 44 22) (endpointMeanBox 44 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 44 22 h) (endpointMeanCornerA 44 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 22, endpointJoint24Q (endpointMeanCornerK 44 22 h) (endpointMeanCornerA 44 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 44 22, endpointRunWeightQ (endpointMeanCutoff 44 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 44 22) = (367923401/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 44 22 h = (logRoundedQ ((endpointMeanCutoff 44 22:ℚ)/200)).2+(367923401/1000000000000000:ℚ)+((endpointMeanRuns 44 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 44 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 44 22) r*endpointJoint24Q (endpointMeanCornerK 44 22 h) (endpointMeanCornerA 44 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 44 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 44 22 h≤endpointMeanCorner 44 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 44 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint44_22

namespace EndpointAnalyticJoint44_23
private noncomputable def weights : IntegerLookupTree := (.branch 2380 (.leaf (106421766700000:ℤ)) (.leaf (6630292400000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2222815126058545:ℤ)) (.leaf (2887597580036675:ℤ))), (.branch 124 (.leaf (2248454120345904:ℤ)) (.leaf (2943424727133114:ℤ))), (.branch 124 (.leaf (2255151152091791:ℤ)) (.leaf (2992765017866204:ℤ))), (.branch 124 (.leaf (2282596000084194:ℤ)) (.leaf (3055373866534602:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 44 23) 8000 (endpointMeanRuns 44 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 44 23, EndpointRunConditions (endpointMeanCutoff 44 23) (endpointMeanBox 44 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 44 23 h) (endpointMeanCornerA 44 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 23, endpointJoint24Q (endpointMeanCornerK 44 23 h) (endpointMeanCornerA 44 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 44 23, endpointRunWeightQ (endpointMeanCutoff 44 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 44 23) = (45853017/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 44 23 h = (logRoundedQ ((endpointMeanCutoff 44 23:ℚ)/200)).2+(45853017/125000000000000:ℚ)+((endpointMeanRuns 44 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 44 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 44 23) r*endpointJoint24Q (endpointMeanCornerK 44 23 h) (endpointMeanCornerA 44 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 44 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 44 23 h≤endpointMeanCorner 44 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 44 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint44_23

namespace EndpointAnalyticJoint44_24
private noncomputable def weights : IntegerLookupTree := (.branch 2380 (.leaf (102932040300000:ℤ)) (.leaf (6596467300000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2248454120345904:ℤ)) (.leaf (2943424727133114:ℤ))), (.branch 124 (.leaf (2274388846842551:ℤ)) (.leaf (3000331204110727:ℤ))), (.branch 124 (.leaf (2282596000084194:ℤ)) (.leaf (3055373866534602:ℤ))), (.branch 124 (.leaf (2310374847720312:ℤ)) (.leaf (3119292496595181:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 44 24) 8000 (endpointMeanRuns 44 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 44 24, EndpointRunConditions (endpointMeanCutoff 44 24) (endpointMeanBox 44 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 44 24 h) (endpointMeanCornerA 44 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 24, endpointJoint24Q (endpointMeanCornerK 44 24 h) (endpointMeanCornerA 44 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 44 24, endpointRunWeightQ (endpointMeanCutoff 44 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 44 24) = (365614917/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 44 24 h = (logRoundedQ ((endpointMeanCutoff 44 24:ℚ)/200)).2+(365614917/1000000000000000:ℚ)+((endpointMeanRuns 44 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 44 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 44 24) r*endpointJoint24Q (endpointMeanCornerK 44 24 h) (endpointMeanCornerA 44 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 44 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 44 24 h≤endpointMeanCorner 44 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 44 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint44_24

namespace EndpointAnalyticJoint44_25
private noncomputable def weights : IntegerLookupTree := (.branch 2380 (.leaf (99890319600000:ℤ)) (.leaf (6566325500000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2274388846842551:ℤ)) (.leaf (3000331204110727:ℤ))), (.branch 124 (.leaf (2300622716662769:ℤ)) (.leaf (3058337878111262:ℤ))), (.branch 124 (.leaf (2310374847720312:ℤ)) (.leaf (3119292496595181:ℤ))), (.branch 124 (.leaf (2338491759725229:ℤ)) (.leaf (3184548308764167:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 44 25) 8000 (endpointMeanRuns 44 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 44 25, EndpointRunConditions (endpointMeanCutoff 44 25) (endpointMeanBox 44 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 44 25 h) (endpointMeanCornerA 44 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 25, endpointJoint24Q (endpointMeanCornerK 44 25 h) (endpointMeanCornerA 44 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 44 25, endpointRunWeightQ (endpointMeanCutoff 44 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 44 25) = (182268687/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 44 25 h = (logRoundedQ ((endpointMeanCutoff 44 25:ℚ)/200)).2+(182268687/500000000000000:ℚ)+((endpointMeanRuns 44 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 44 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 44 25) r*endpointJoint24Q (endpointMeanCornerK 44 25 h) (endpointMeanCornerA 44 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 44 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 44 25 h≤endpointMeanCorner 44 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 44 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint44_25

namespace EndpointAnalyticJoint44_26
private noncomputable def weights : IntegerLookupTree := (.branch 2380 (.leaf (96939398100000:ℤ)) (.leaf (6536463300000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2300622716662769:ℤ)) (.leaf (3058337878111262:ℤ))), (.branch 124 (.leaf (2327159180266233:ℤ)) (.leaf (3117466019709780:ℤ))), (.branch 124 (.leaf (2338491759725229:ℤ)) (.leaf (3184548308764167:ℤ))), (.branch 124 (.leaf (2366950850291117:ℤ)) (.leaf (3251169276982638:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 44 26) 8000 (endpointMeanRuns 44 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 44 26, EndpointRunConditions (endpointMeanCutoff 44 26) (endpointMeanBox 44 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 44 26 h) (endpointMeanCornerA 44 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 26, endpointJoint24Q (endpointMeanCornerK 44 26 h) (endpointMeanCornerA 44 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 44 26, endpointRunWeightQ (endpointMeanCutoff 44 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 44 26) = (14538793/40000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 44 26 h = (logRoundedQ ((endpointMeanCutoff 44 26:ℚ)/200)).2+(14538793/40000000000000:ℚ)+((endpointMeanRuns 44 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 44 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 44 26) r*endpointJoint24Q (endpointMeanCornerK 44 26 h) (endpointMeanCornerA 44 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 44 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 44 26 h≤endpointMeanCorner 44 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 44 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint44_26

namespace EndpointAnalyticJoint44_27
private noncomputable def weights : IntegerLookupTree := (.leaf (173115788900000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2327159180266233:ℤ)), (.leaf (2354001727911849:ℤ)), (.leaf (2366950850291117:ℤ)), (.leaf (2395756283679235:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 44 27) 8000 (endpointMeanRuns 44 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 44 27, EndpointRunConditions (endpointMeanCutoff 44 27) (endpointMeanBox 44 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 44 27 h) (endpointMeanCornerA 44 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 27, endpointJoint24Q (endpointMeanCornerK 44 27 h) (endpointMeanCornerA 44 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 44 27, endpointRunWeightQ (endpointMeanCutoff 44 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 44 27) = (72459031/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 44 27 h = (logRoundedQ ((endpointMeanCutoff 44 27:ℚ)/200)).2+(72459031/200000000000000:ℚ)+((endpointMeanRuns 44 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 44 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 44 27) r*endpointJoint24Q (endpointMeanCornerK 44 27 h) (endpointMeanCornerA 44 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 44 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 44 27 h≤endpointMeanCorner 44 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 44 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint44_27

namespace EndpointAnalyticJoint44_28
private noncomputable def weights : IntegerLookupTree := (.leaf (168720333900000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2354001727911849:ℤ)), (.leaf (2381153890116803:ℤ)), (.leaf (2395756283679235:ℤ)), (.leaf (2424912274829290:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 44 28) 8000 (endpointMeanRuns 44 28) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 44 28, EndpointRunConditions (endpointMeanCutoff 44 28) (endpointMeanBox 44 28).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 28, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 44 28 h) (endpointMeanCornerA 44 28 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 28, endpointJoint24Q (endpointMeanCornerK 44 28 h) (endpointMeanCornerA 44 28 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 44 28, endpointRunWeightQ (endpointMeanCutoff 44 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 44 28) = (72249621/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 44 28 h = (logRoundedQ ((endpointMeanCutoff 44 28:ℚ)/200)).2+(72249621/200000000000000:ℚ)+((endpointMeanRuns 44 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 44 28).map (fun r => endpointRunWeightQ (endpointMeanCutoff 44 28) r*endpointJoint24Q (endpointMeanCornerK 44 28 h) (endpointMeanCornerA 44 28 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 44 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 44 28 h≤endpointMeanCorner 44 28 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 44 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint44_28

namespace EndpointAnalyticJoint44_29
private noncomputable def weights : IntegerLookupTree := (.leaf (165381466500000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2381153890116803:ℤ)), (.leaf (2397595286355932:ℤ)), (.leaf (2424912274829290:ℤ)), (.leaf (2442575909846226:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 44 29) 8000 (endpointMeanRuns 44 29) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 44 29, EndpointRunConditions (endpointMeanCutoff 44 29) (endpointMeanBox 44 29).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 29, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 44 29 h) (endpointMeanCornerA 44 29 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 29, endpointJoint24Q (endpointMeanCornerK 44 29 h) (endpointMeanCornerA 44 29 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 44 29, endpointRunWeightQ (endpointMeanCutoff 44 29) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 44 29) = (72088053/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 44 29 h = (logRoundedQ ((endpointMeanCutoff 44 29:ℚ)/200)).2+(72088053/200000000000000:ℚ)+((endpointMeanRuns 44 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 44 29).map (fun r => endpointRunWeightQ (endpointMeanCutoff 44 29) r*endpointJoint24Q (endpointMeanCornerK 44 29 h) (endpointMeanCornerA 44 29 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 44 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 44 29 h≤endpointMeanCorner 44 29 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 44 29 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint44_29

namespace EndpointAnalyticJoint44_30
private noncomputable def weights : IntegerLookupTree := (.branch 1970 (.leaf (70417796400000:ℤ)) (.leaf (17688250400000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 129 (.leaf (2397595286355932:ℤ)) (.leaf (3707747678848252:ℤ))), (.branch 129 (.leaf (2408619238120926:ℤ)) (.leaf (3741238932351296:ℤ))), (.branch 129 (.leaf (2442575909846226:ℤ)) (.leaf (3949612193647216:ℤ))), (.branch 129 (.leaf (2454423089976142:ℤ)) (.leaf (3988692872241345:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 44 30) 8000 (endpointMeanRuns 44 30) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 44 30, EndpointRunConditions (endpointMeanCutoff 44 30) (endpointMeanBox 44 30).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 30, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 44 30 h) (endpointMeanCornerA 44 30 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 30, endpointJoint24Q (endpointMeanCornerK 44 30 h) (endpointMeanCornerA 44 30 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 44 30, endpointRunWeightQ (endpointMeanCutoff 44 30) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 44 30) = (359866689/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 44 30 h = (logRoundedQ ((endpointMeanCutoff 44 30:ℚ)/200)).2+(359866689/1000000000000000:ℚ)+((endpointMeanRuns 44 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 44 30).map (fun r => endpointRunWeightQ (endpointMeanCutoff 44 30) r*endpointJoint24Q (endpointMeanCornerK 44 30 h) (endpointMeanCornerA 44 30 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 44 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 44 30 h≤endpointMeanCorner 44 30 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 44 30 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint44_30

namespace EndpointAnalyticJoint44_31
private noncomputable def weights : IntegerLookupTree := (.leaf (159815535800000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2408619238120926:ℤ)), (.leaf (2436401384356411:ℤ)), (.leaf (2454423089976142:ℤ)), (.leaf (2484293047274103:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 44 31) 8000 (endpointMeanRuns 44 31) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 44 31, EndpointRunConditions (endpointMeanCutoff 44 31) (endpointMeanBox 44 31).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 31, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 44 31 h) (endpointMeanCornerA 44 31 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 31, endpointJoint24Q (endpointMeanCornerK 44 31 h) (endpointMeanCornerA 44 31 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 44 31, endpointRunWeightQ (endpointMeanCutoff 44 31) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 44 31) = (89767113/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 44 31 h = (logRoundedQ ((endpointMeanCutoff 44 31:ℚ)/200)).2+(89767113/250000000000000:ℚ)+((endpointMeanRuns 44 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 44 31).map (fun r => endpointRunWeightQ (endpointMeanCutoff 44 31) r*endpointJoint24Q (endpointMeanCornerK 44 31 h) (endpointMeanCornerA 44 31 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 44 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 44 31 h≤endpointMeanCorner 44 31 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 44 31 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint44_31

namespace EndpointAnalyticJoint44_32
private noncomputable def weights : IntegerLookupTree := (.leaf (155768196500000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2436401384356411:ℤ)), (.leaf (2464503982922937:ℤ)), (.leaf (2484293047274103:ℤ)), (.leaf (2514526517428767:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 44 32) 8000 (endpointMeanRuns 44 32) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 44 32, EndpointRunConditions (endpointMeanCutoff 44 32) (endpointMeanBox 44 32).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 32, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 44 32 h) (endpointMeanCornerA 44 32 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 32, endpointJoint24Q (endpointMeanCornerK 44 32 h) (endpointMeanCornerA 44 32 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 44 32, endpointRunWeightQ (endpointMeanCutoff 44 32) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 44 32) = (71610043/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 44 32 h = (logRoundedQ ((endpointMeanCutoff 44 32:ℚ)/200)).2+(71610043/200000000000000:ℚ)+((endpointMeanRuns 44 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 44 32).map (fun r => endpointRunWeightQ (endpointMeanCutoff 44 32) r*endpointJoint24Q (endpointMeanCornerK 44 32 h) (endpointMeanCornerA 44 32 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 44 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 44 32 h≤endpointMeanCorner 44 32 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 44 32 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint44_32

namespace EndpointAnalyticJoint44_33
private noncomputable def weights : IntegerLookupTree := (.leaf (151826483500000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2464503982922937:ℤ)), (.leaf (2492930730068290:ℤ)), (.leaf (2514526517428767:ℤ)), (.leaf (2545127924336541:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 44 33) 8000 (endpointMeanRuns 44 33) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 44 33, EndpointRunConditions (endpointMeanCutoff 44 33) (endpointMeanBox 44 33).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 33, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 44 33 h) (endpointMeanCornerA 44 33 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 44 33, endpointJoint24Q (endpointMeanCornerK 44 33 h) (endpointMeanCornerA 44 33 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 44 33, endpointRunWeightQ (endpointMeanCutoff 44 33) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 44 33) = (178520453/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 44 33 h = (logRoundedQ ((endpointMeanCutoff 44 33:ℚ)/200)).2+(178520453/500000000000000:ℚ)+((endpointMeanRuns 44 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 44 33).map (fun r => endpointRunWeightQ (endpointMeanCutoff 44 33) r*endpointJoint24Q (endpointMeanCornerK 44 33 h) (endpointMeanCornerA 44 33 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 44 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 44 33 h≤endpointMeanCorner 44 33 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 44 33 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint44_33

namespace EndpointAnalyticJoint45_21
private noncomputable def weights : IntegerLookupTree := (.branch 2344 (.leaf (104086194500000:ℤ)) (.leaf (7230752800000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2213398286932133:ℤ)) (.leaf (2898551903983389:ℤ))), (.branch 124 (.leaf (2228036287890346:ℤ)) (.leaf (2931439111352456:ℤ))), (.branch 124 (.leaf (2246722846825258:ℤ)) (.leaf (3016777629828203:ℤ))), (.branch 124 (.leaf (2262439763381608:ℤ)) (.leaf (3054105714404050:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 21) 8000 (endpointMeanRuns 45 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 45 21, EndpointRunConditions (endpointMeanCutoff 45 21) (endpointMeanBox 45 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 45 21 h) (endpointMeanCornerA 45 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 21, endpointJoint24Q (endpointMeanCornerK 45 21 h) (endpointMeanCornerA 45 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 45 21, endpointRunWeightQ (endpointMeanCutoff 45 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 45 21) = (366097081/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 45 21 h = (logRoundedQ ((endpointMeanCutoff 45 21:ℚ)/200)).2+(366097081/1000000000000000:ℚ)+((endpointMeanRuns 45 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 45 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 45 21) r*endpointJoint24Q (endpointMeanCornerK 45 21 h) (endpointMeanCornerA 45 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 45 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 45 21 h≤endpointMeanCorner 45 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 45 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint45_21

namespace EndpointAnalyticJoint45_22
private noncomputable def weights : IntegerLookupTree := (.branch 2344 (.leaf (101681115600000:ℤ)) (.leaf (7204804400000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2228036287890346:ℤ)) (.leaf (2931439111352456:ℤ))), (.branch 124 (.leaf (2255151152091791:ℤ)) (.leaf (2992765017866204:ℤ))), (.branch 124 (.leaf (2262439763381608:ℤ)) (.leaf (3054105714404050:ℤ))), (.branch 124 (.leaf (2291568851655245:ℤ)) (.leaf (3123813103131433:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 22) 8000 (endpointMeanRuns 45 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 45 22, EndpointRunConditions (endpointMeanCutoff 45 22) (endpointMeanBox 45 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 45 22 h) (endpointMeanCornerA 45 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 22, endpointJoint24Q (endpointMeanCornerK 45 22 h) (endpointMeanCornerA 45 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 45 22, endpointRunWeightQ (endpointMeanCutoff 45 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 45 22) = (182627307/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 45 22 h = (logRoundedQ ((endpointMeanCutoff 45 22:ℚ)/200)).2+(182627307/500000000000000:ℚ)+((endpointMeanRuns 45 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 45 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 45 22) r*endpointJoint24Q (endpointMeanCornerK 45 22 h) (endpointMeanCornerA 45 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 45 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 45 22 h≤endpointMeanCorner 45 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 45 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint45_22

namespace EndpointAnalyticJoint45_23
private noncomputable def weights : IntegerLookupTree := (.branch 1758 (.leaf (73697783300000:ℤ)) (.leaf (30174973500000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 130 (.leaf (2255151152091791:ℤ)) (.leaf (3445289424125894:ℤ))), (.branch 130 (.leaf (2282596000084194:ℤ)) (.leaf (3534352085411303:ℤ))), (.branch 130 (.leaf (2291568851655245:ℤ)) (.leaf (3682222251824307:ℤ))), (.branch 130 (.leaf (2321072979210538:ℤ)) (.leaf (3788348609603546:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 23) 8000 (endpointMeanRuns 45 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 45 23, EndpointRunConditions (endpointMeanCutoff 45 23) (endpointMeanBox 45 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 45 23 h) (endpointMeanCornerA 45 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 23, endpointJoint24Q (endpointMeanCornerK 45 23 h) (endpointMeanCornerA 45 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 45 23, endpointRunWeightQ (endpointMeanCutoff 45 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 45 23) = (364180423/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 45 23 h = (logRoundedQ ((endpointMeanCutoff 45 23:ℚ)/200)).2+(364180423/1000000000000000:ℚ)+((endpointMeanRuns 45 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 45 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 45 23) r*endpointJoint24Q (endpointMeanCornerK 45 23 h) (endpointMeanCornerA 45 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 45 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 45 23 h≤endpointMeanCorner 45 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 45 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint45_23

namespace EndpointAnalyticJoint45_24
private noncomputable def weights : IntegerLookupTree := (.branch 2009 (.leaf (80659819000000:ℤ)) (.leaf (16318606400000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 128 (.leaf (2282596000084194:ℤ)) (.leaf (3353885969985400:ℤ))), (.branch 128 (.leaf (2310374847720312:ℤ)) (.leaf (3434511319997188:ℤ))), (.branch 128 (.leaf (2321072979210538:ℤ)) (.leaf (3559162926661070:ℤ))), (.branch 128 (.leaf (2350956974707464:ℤ)) (.leaf (3653755740616242:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 24) 8000 (endpointMeanRuns 45 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 45 24, EndpointRunConditions (endpointMeanCutoff 45 24) (endpointMeanBox 45 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 45 24 h) (endpointMeanCornerA 45 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 24, endpointJoint24Q (endpointMeanCornerK 45 24 h) (endpointMeanCornerA 45 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 45 24, endpointRunWeightQ (endpointMeanCutoff 45 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 45 24) = (181499259/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 45 24 h = (logRoundedQ ((endpointMeanCutoff 45 24:ℚ)/200)).2+(181499259/500000000000000:ℚ)+((endpointMeanRuns 45 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 45 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 45 24) r*endpointJoint24Q (endpointMeanCornerK 45 24 h) (endpointMeanCornerA 45 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 45 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 45 24 h≤endpointMeanCorner 45 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 45 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint45_24

namespace EndpointAnalyticJoint45_25
private noncomputable def weights : IntegerLookupTree := (.branch 2344 (.leaf (92608251500000:ℤ)) (.leaf (7102869400000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2310374847720312:ℤ)) (.leaf (3119292496595181:ℤ))), (.branch 124 (.leaf (2338491759725229:ℤ)) (.leaf (3184548308764167:ℤ))), (.branch 124 (.leaf (2350956974707464:ℤ)) (.leaf (3268037231284087:ℤ))), (.branch 124 (.leaf (2381225728975382:ℤ)) (.leaf (3342627426568514:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 25) 8000 (endpointMeanRuns 45 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 45 25, EndpointRunConditions (endpointMeanCutoff 45 25) (endpointMeanBox 45 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 45 25 h) (endpointMeanCornerA 45 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 25, endpointJoint24Q (endpointMeanCornerK 45 25 h) (endpointMeanCornerA 45 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 45 25, endpointRunWeightQ (endpointMeanCutoff 45 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 45 25) = (361945079/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 45 25 h = (logRoundedQ ((endpointMeanCutoff 45 25:ℚ)/200)).2+(361945079/1000000000000000:ℚ)+((endpointMeanRuns 45 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 45 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 45 25) r*endpointJoint24Q (endpointMeanCornerK 45 25 h) (endpointMeanCornerA 45 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 45 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 45 25 h≤endpointMeanCorner 45 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 45 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint45_25

namespace EndpointAnalyticJoint45_26
private noncomputable def weights : IntegerLookupTree := (.branch 1940 (.leaf (72005547900000:ℤ)) (.leaf (19112185100000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 129 (.leaf (2338491759725229:ℤ)) (.leaf (3614674341143338:ℤ))), (.branch 129 (.leaf (2366950850291117:ℤ)) (.leaf (3704755329546070:ℤ))), (.branch 129 (.leaf (2381225728975382:ℤ)) (.leaf (3874705123171328:ℤ))), (.branch 129 (.leaf (2411884195813456:ℤ)) (.leaf (3981891085400777:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 26) 8000 (endpointMeanRuns 45 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 45 26, EndpointRunConditions (endpointMeanCutoff 45 26) (endpointMeanBox 45 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 45 26 h) (endpointMeanCornerA 45 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 26, endpointJoint24Q (endpointMeanCornerK 45 26 h) (endpointMeanCornerA 45 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 45 26, endpointRunWeightQ (endpointMeanCutoff 45 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 45 26) = (90196447/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 45 26 h = (logRoundedQ ((endpointMeanCutoff 45 26:ℚ)/200)).2+(90196447/250000000000000:ℚ)+((endpointMeanRuns 45 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 45 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 45 26) r*endpointJoint24Q (endpointMeanCornerK 45 26 h) (endpointMeanCornerA 45 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 45 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 45 26 h≤endpointMeanCorner 45 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 45 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint45_26

namespace EndpointAnalyticJoint45_27
private noncomputable def weights : IntegerLookupTree := (.leaf (162573913100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2366950850291117:ℤ)), (.leaf (2395756283679235:ℤ)), (.leaf (2411884195813456:ℤ)), (.leaf (2442937392801391:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 27) 8000 (endpointMeanRuns 45 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 45 27, EndpointRunConditions (endpointMeanCutoff 45 27) (endpointMeanBox 45 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 45 27 h) (endpointMeanCornerA 45 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 27, endpointJoint24Q (endpointMeanCornerK 45 27 h) (endpointMeanCornerA 45 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 45 27, endpointRunWeightQ (endpointMeanCutoff 45 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 45 27) = (71950463/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 45 27 h = (logRoundedQ ((endpointMeanCutoff 45 27:ℚ)/200)).2+(71950463/200000000000000:ℚ)+((endpointMeanRuns 45 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 45 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 45 27) r*endpointJoint24Q (endpointMeanCornerK 45 27 h) (endpointMeanCornerA 45 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 45 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 45 27 h≤endpointMeanCorner 45 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 45 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint45_27

namespace EndpointAnalyticJoint45_28
private noncomputable def weights : IntegerLookupTree := (.leaf (158454504100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2395756283679235:ℤ)), (.leaf (2424912274829290:ℤ)), (.leaf (2442937392801391:ℤ)), (.leaf (2474390402120637:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 28) 8000 (endpointMeanRuns 45 28) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 45 28, EndpointRunConditions (endpointMeanCutoff 45 28) (endpointMeanBox 45 28).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 28, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 45 28 h) (endpointMeanCornerA 45 28 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 28, endpointJoint24Q (endpointMeanCornerK 45 28 h) (endpointMeanCornerA 45 28 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 45 28, endpointRunWeightQ (endpointMeanCutoff 45 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 45 28) = (179364019/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 45 28 h = (logRoundedQ ((endpointMeanCutoff 45 28:ℚ)/200)).2+(179364019/500000000000000:ℚ)+((endpointMeanRuns 45 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 45 28).map (fun r => endpointRunWeightQ (endpointMeanCutoff 45 28) r*endpointJoint24Q (endpointMeanCornerK 45 28 h) (endpointMeanCornerA 45 28 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 45 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 45 28 h≤endpointMeanCorner 45 28 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 45 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint45_28

namespace EndpointAnalyticJoint45_29
private noncomputable def weights : IntegerLookupTree := (.leaf (154883235300000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2424912274829290:ℤ)), (.leaf (2442575909846226:ℤ)), (.leaf (2474390402120637:ℤ)), (.leaf (2493456256291830:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 29) 8000 (endpointMeanRuns 45 29) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 45 29, EndpointRunConditions (endpointMeanCutoff 45 29) (endpointMeanBox 45 29).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 29, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 45 29 h) (endpointMeanCornerA 45 29 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 29, endpointJoint24Q (endpointMeanCornerK 45 29 h) (endpointMeanCornerA 45 29 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 45 29, endpointRunWeightQ (endpointMeanCutoff 45 29) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 45 29) = (178912579/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 45 29 h = (logRoundedQ ((endpointMeanCutoff 45 29:ℚ)/200)).2+(178912579/500000000000000:ℚ)+((endpointMeanRuns 45 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 45 29).map (fun r => endpointRunWeightQ (endpointMeanCutoff 45 29) r*endpointJoint24Q (endpointMeanCornerK 45 29 h) (endpointMeanCornerA 45 29 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 45 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 45 29 h≤endpointMeanCorner 45 29 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 45 29 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint45_29

namespace EndpointAnalyticJoint45_30
private noncomputable def weights : IntegerLookupTree := (.leaf (152693441100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2442575909846226:ℤ)), (.leaf (2454423089976142:ℤ)), (.leaf (2493456256291830:ℤ)), (.leaf (2506248371386113:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 30) 8000 (endpointMeanRuns 45 30) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 45 30, EndpointRunConditions (endpointMeanCutoff 45 30) (endpointMeanBox 45 30).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 30, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 45 30 h) (endpointMeanCornerA 45 30 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 30, endpointJoint24Q (endpointMeanCornerK 45 30 h) (endpointMeanCornerA 45 30 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 45 30, endpointRunWeightQ (endpointMeanCutoff 45 30) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 45 30) = (357264433/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 45 30 h = (logRoundedQ ((endpointMeanCutoff 45 30:ℚ)/200)).2+(357264433/1000000000000000:ℚ)+((endpointMeanRuns 45 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 45 30).map (fun r => endpointRunWeightQ (endpointMeanCutoff 45 30) r*endpointJoint24Q (endpointMeanCornerK 45 30 h) (endpointMeanCornerA 45 30 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 45 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 45 30 h≤endpointMeanCorner 45 30 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 45 30 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint45_30

namespace EndpointAnalyticJoint45_31
private noncomputable def weights : IntegerLookupTree := (.leaf (150107755500000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2454423089976142:ℤ)), (.leaf (2484293047274103:ℤ)), (.leaf (2506248371386113:ℤ)), (.leaf (2538516514488688:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 31) 8000 (endpointMeanRuns 45 31) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 45 31, EndpointRunConditions (endpointMeanCutoff 45 31) (endpointMeanBox 45 31).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 31, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 45 31 h) (endpointMeanCornerA 45 31 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 31, endpointJoint24Q (endpointMeanCornerK 45 31 h) (endpointMeanCornerA 45 31 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 45 31, endpointRunWeightQ (endpointMeanCutoff 45 31) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 45 31) = (356595149/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 45 31 h = (logRoundedQ ((endpointMeanCutoff 45 31:ℚ)/200)).2+(356595149/1000000000000000:ℚ)+((endpointMeanRuns 45 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 45 31).map (fun r => endpointRunWeightQ (endpointMeanCutoff 45 31) r*endpointJoint24Q (endpointMeanCornerK 45 31 h) (endpointMeanCornerA 45 31 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 45 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 45 31 h≤endpointMeanCorner 45 31 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 45 31 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint45_31

namespace EndpointAnalyticJoint45_32
private noncomputable def weights : IntegerLookupTree := (.leaf (145898087000000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2484293047274103:ℤ)), (.leaf (2514526517428767:ℤ)), (.leaf (2538516514488688:ℤ)), (.leaf (2571200112448485:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 32) 8000 (endpointMeanRuns 45 32) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 45 32, EndpointRunConditions (endpointMeanCutoff 45 32) (endpointMeanBox 45 32).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 32, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 45 32 h) (endpointMeanCornerA 45 32 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 32, endpointJoint24Q (endpointMeanCornerK 45 32 h) (endpointMeanCornerA 45 32 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 45 32, endpointRunWeightQ (endpointMeanCutoff 45 32) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 45 32) = (1421953/4000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 45 32 h = (logRoundedQ ((endpointMeanCutoff 45 32:ℚ)/200)).2+(1421953/4000000000000:ℚ)+((endpointMeanRuns 45 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 45 32).map (fun r => endpointRunWeightQ (endpointMeanCutoff 45 32) r*endpointJoint24Q (endpointMeanCornerK 45 32 h) (endpointMeanCornerA 45 32 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 45 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 45 32 h≤endpointMeanCorner 45 32 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 45 32 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint45_32

namespace EndpointAnalyticJoint45_33
private noncomputable def weights : IntegerLookupTree := (.leaf (142213356700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2514526517428767:ℤ)), (.leaf (2545127924336541:ℤ)), (.leaf (2571200112448485:ℤ)), (.leaf (2604304514279163:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 33) 8000 (endpointMeanRuns 45 33) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 45 33, EndpointRunConditions (endpointMeanCutoff 45 33) (endpointMeanBox 45 33).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 33, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 45 33 h) (endpointMeanCornerA 45 33 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 33, endpointJoint24Q (endpointMeanCornerK 45 33 h) (endpointMeanCornerA 45 33 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 45 33, endpointRunWeightQ (endpointMeanCutoff 45 33) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 45 33) = (17725053/50000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 45 33 h = (logRoundedQ ((endpointMeanCutoff 45 33:ℚ)/200)).2+(17725053/50000000000000:ℚ)+((endpointMeanRuns 45 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 45 33).map (fun r => endpointRunWeightQ (endpointMeanCutoff 45 33) r*endpointJoint24Q (endpointMeanCornerK 45 33 h) (endpointMeanCornerA 45 33 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 45 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 45 33 h≤endpointMeanCorner 45 33 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 45 33 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint45_33

namespace EndpointAnalyticJoint45_34
private noncomputable def weights : IntegerLookupTree := (.leaf (139413764100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2545127924336541:ℤ)), (.leaf (2555410929394709:ℤ)), (.leaf (2604304514279163:ℤ)), (.leaf (2615433761284008:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 45 34) 8000 (endpointMeanRuns 45 34) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 45 34, EndpointRunConditions (endpointMeanCutoff 45 34) (endpointMeanBox 45 34).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 34, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 45 34 h) (endpointMeanCornerA 45 34 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 45 34, endpointJoint24Q (endpointMeanCornerK 45 34 h) (endpointMeanCornerA 45 34 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 45 34, endpointRunWeightQ (endpointMeanCutoff 45 34) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 45 34) = (22108691/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 45 34 h = (logRoundedQ ((endpointMeanCutoff 45 34:ℚ)/200)).2+(22108691/62500000000000:ℚ)+((endpointMeanRuns 45 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 45 34).map (fun r => endpointRunWeightQ (endpointMeanCutoff 45 34) r*endpointJoint24Q (endpointMeanCornerK 45 34 h) (endpointMeanCornerA 45 34 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 45 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 45 34 h≤endpointMeanCorner 45 34 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 45 34 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint45_34

namespace EndpointAnalyticJoint46_22
private noncomputable def weights : IntegerLookupTree := (.branch 2131 (.leaf (86110567800000:ℤ)) (.leaf (12850053900000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 126 (.leaf (2244246969658342:ℤ)) (.leaf (3240475251078238:ℤ))), (.branch 126 (.leaf (2259299673570765:ℤ)) (.leaf (3283221340598563:ℤ))), (.branch 126 (.leaf (2281742120255899:ℤ)) (.leaf (3442639099853788:ℤ))), (.branch 126 (.leaf (2297960482522097:ℤ)) (.leaf (3493124874776927:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 46 22) 8000 (endpointMeanRuns 46 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 46 22, EndpointRunConditions (endpointMeanCutoff 46 22) (endpointMeanBox 46 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 46 22 h) (endpointMeanCornerA 46 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 22, endpointJoint24Q (endpointMeanCornerK 46 22 h) (endpointMeanCornerA 46 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 46 22, endpointRunWeightQ (endpointMeanCutoff 46 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 46 22) = (90603021/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 46 22 h = (logRoundedQ ((endpointMeanCutoff 46 22:ℚ)/200)).2+(90603021/250000000000000:ℚ)+((endpointMeanRuns 46 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 46 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 46 22) r*endpointJoint24Q (endpointMeanCornerK 46 22 h) (endpointMeanCornerA 46 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 46 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 46 22 h≤endpointMeanCorner 46 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 46 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint46_22

namespace EndpointAnalyticJoint46_23
private noncomputable def weights : IntegerLookupTree := (.branch 2052 (.leaf (80443780900000:ℤ)) (.leaf (15515765000000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 127 (.leaf (2259299673570765:ℤ)) (.leaf (3371690934939605:ℤ))), (.branch 127 (.leaf (2287474972261847:ℤ)) (.leaf (3457859608682780:ℤ))), (.branch 127 (.leaf (2297960482522097:ℤ)) (.leaf (3606825262107528:ℤ))), (.branch 127 (.leaf (2328334891755808:ℤ)) (.leaf (3709860925537977:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 46 23) 8000 (endpointMeanRuns 46 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 46 23, EndpointRunConditions (endpointMeanCutoff 46 23) (endpointMeanBox 46 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 46 23 h) (endpointMeanCornerA 46 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 23, endpointJoint24Q (endpointMeanCornerK 46 23 h) (endpointMeanCornerA 46 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 46 23, endpointRunWeightQ (endpointMeanCutoff 46 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 46 23) = (11299877/31250000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 46 23 h = (logRoundedQ ((endpointMeanCutoff 46 23:ℚ)/200)).2+(11299877/31250000000000:ℚ)+((endpointMeanRuns 46 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 46 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 46 23) r*endpointJoint24Q (endpointMeanCornerK 46 23 h) (endpointMeanCornerA 46 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 46 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 46 23 h≤endpointMeanCorner 46 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 46 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint46_23

namespace EndpointAnalyticJoint46_24
private noncomputable def weights : IntegerLookupTree := (.branch 2409 (.leaf (92119242900000:ℤ)) (.leaf (6438043600000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 123 (.leaf (2287474972261847:ℤ)) (.leaf (3118793065288263:ℤ))), (.branch 123 (.leaf (2316001639771156:ℤ)) (.leaf (3187429128274175:ℤ))), (.branch 123 (.leaf (2328334891755808:ℤ)) (.leaf (3282334489529501:ℤ))), (.branch 123 (.leaf (2359110789502181:ℤ)) (.leaf (3361720931468339:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 46 24) 8000 (endpointMeanRuns 46 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 46 24, EndpointRunConditions (endpointMeanCutoff 46 24) (endpointMeanBox 46 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 46 24 h) (endpointMeanCornerA 46 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 24, endpointJoint24Q (endpointMeanCornerK 46 24 h) (endpointMeanCornerA 46 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 46 24, endpointRunWeightQ (endpointMeanCutoff 46 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 46 24) = (72088053/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 46 24 h = (logRoundedQ ((endpointMeanCutoff 46 24:ℚ)/200)).2+(72088053/200000000000000:ℚ)+((endpointMeanRuns 46 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 46 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 46 24) r*endpointJoint24Q (endpointMeanCornerK 46 24 h) (endpointMeanCornerA 46 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 46 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 46 24 h≤endpointMeanCorner 46 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 46 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint46_24

namespace EndpointAnalyticJoint46_25
private noncomputable def weights : IntegerLookupTree := (.branch 2217 (.leaf (81983733600000:ℤ)) (.leaf (10269847900000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2316001639771156:ℤ)) (.leaf (3354237661648989:ℤ))), (.branch 125 (.leaf (2344884057952740:ℤ)) (.leaf (3433683188230938:ℤ))), (.branch 125 (.leaf (2359110789502181:ℤ)) (.leaf (3569188144920647:ℤ))), (.branch 125 (.leaf (2390293482630721:ℤ)) (.leaf (3662813932122933:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 46 25) 8000 (endpointMeanRuns 46 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 46 25, EndpointRunConditions (endpointMeanCutoff 46 25) (endpointMeanBox 46 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 46 25 h) (endpointMeanCornerA 46 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 25, endpointJoint24Q (endpointMeanCornerK 46 25 h) (endpointMeanCornerA 46 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 46 25, endpointRunWeightQ (endpointMeanCutoff 46 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 46 25) = (89823989/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 46 25 h = (logRoundedQ ((endpointMeanCutoff 46 25:ℚ)/200)).2+(89823989/250000000000000:ℚ)+((endpointMeanRuns 46 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 46 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 46 25) r*endpointJoint24Q (endpointMeanCornerK 46 25 h) (endpointMeanCornerA 46 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 46 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 46 25 h≤endpointMeanCorner 46 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 46 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint46_25

namespace EndpointAnalyticJoint46_26
private noncomputable def weights : IntegerLookupTree := (.branch 1979 (.leaf (74062105300000:ℤ)) (.leaf (18228408600000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 126 (.leaf (2344884057952740:ℤ)) (.leaf (3531473765862798:ℤ))), (.branch 126 (.leaf (2374126663305909:ℤ)) (.leaf (3618327935336008:ℤ))), (.branch 126 (.leaf (2390293482630721:ℤ)) (.leaf (3787742517405829:ℤ))), (.branch 126 (.leaf (2421888348157046:ℤ)) (.leaf (3891370313629872:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 46 26) 8000 (endpointMeanRuns 46 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 46 26, EndpointRunConditions (endpointMeanCutoff 46 26) (endpointMeanBox 46 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 46 26 h) (endpointMeanCornerA 46 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 26, endpointJoint24Q (endpointMeanCornerK 46 26 h) (endpointMeanCornerA 46 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 46 26, endpointRunWeightQ (endpointMeanCutoff 46 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 46 26) = (358275713/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 46 26 h = (logRoundedQ ((endpointMeanCutoff 46 26:ℚ)/200)).2+(358275713/1000000000000000:ℚ)+((endpointMeanRuns 46 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 46 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 46 26) r*endpointJoint24Q (endpointMeanCornerK 46 26 h) (endpointMeanCornerA 46 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 46 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 46 26 h≤endpointMeanCorner 46 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 46 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint46_26

namespace EndpointAnalyticJoint46_27
private noncomputable def weights : IntegerLookupTree := (.leaf (157967922400000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2374126663305909:ℤ)), (.leaf (2403733947656719:ℤ)), (.leaf (2421888348157046:ℤ)), (.leaf (2453900834170094:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 46 27) 8000 (endpointMeanRuns 46 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 46 27, EndpointRunConditions (endpointMeanCutoff 46 27) (endpointMeanBox 46 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 46 27 h) (endpointMeanCornerA 46 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 27, endpointJoint24Q (endpointMeanCornerK 46 27 h) (endpointMeanCornerA 46 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 46 27, endpointRunWeightQ (endpointMeanCutoff 46 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 46 27) = (71430523/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 46 27 h = (logRoundedQ ((endpointMeanCutoff 46 27:ℚ)/200)).2+(71430523/200000000000000:ℚ)+((endpointMeanRuns 46 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 46 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 46 27) r*endpointJoint24Q (endpointMeanCornerK 46 27 h) (endpointMeanCornerA 46 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 46 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 46 27 h≤endpointMeanCorner 46 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 46 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint46_27

namespace EndpointAnalyticJoint46_28
private noncomputable def weights : IntegerLookupTree := (.leaf (154006854200000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2403733947656719:ℤ)), (.leaf (2433710458847940:ℤ)), (.leaf (2453900834170094:ℤ)), (.leaf (2486336460771566:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 46 28) 8000 (endpointMeanRuns 46 28) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 46 28, EndpointRunConditions (endpointMeanCutoff 46 28) (endpointMeanBox 46 28).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 28, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 46 28 h) (endpointMeanCornerA 46 28 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 28, endpointJoint24Q (endpointMeanCornerK 46 28 h) (endpointMeanCornerA 46 28 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 46 28, endpointRunWeightQ (endpointMeanCutoff 46 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 46 28) = (356151111/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 46 28 h = (logRoundedQ ((endpointMeanCutoff 46 28:ℚ)/200)).2+(356151111/1000000000000000:ℚ)+((endpointMeanRuns 46 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 46 28).map (fun r => endpointRunWeightQ (endpointMeanCutoff 46 28) r*endpointJoint24Q (endpointMeanCornerK 46 28 h) (endpointMeanCornerA 46 28 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 46 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 46 28 h≤endpointMeanCorner 46 28 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 46 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint46_28

namespace EndpointAnalyticJoint46_29
private noncomputable def weights : IntegerLookupTree := (.leaf (150571881000000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2433710458847940:ℤ)), (.leaf (2451875507561743:ℤ)), (.leaf (2486336460771566:ℤ)), (.leaf (2506003267866356:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 46 29) 8000 (endpointMeanRuns 46 29) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 46 29, EndpointRunConditions (endpointMeanCutoff 46 29) (endpointMeanBox 46 29).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 29, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 46 29 h) (endpointMeanCornerA 46 29 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 29, endpointJoint24Q (endpointMeanCornerK 46 29 h) (endpointMeanCornerA 46 29 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 46 29, endpointRunWeightQ (endpointMeanCutoff 46 29) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 46 29) = (177634071/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 46 29 h = (logRoundedQ ((endpointMeanCutoff 46 29:ℚ)/200)).2+(177634071/500000000000000:ℚ)+((endpointMeanRuns 46 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 46 29).map (fun r => endpointRunWeightQ (endpointMeanCutoff 46 29) r*endpointJoint24Q (endpointMeanCornerK 46 29 h) (endpointMeanCornerA 46 29 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 46 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 46 29 h≤endpointMeanCorner 46 29 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 46 29 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint46_29

namespace EndpointAnalyticJoint46_30
private noncomputable def weights : IntegerLookupTree := (.leaf (148465203300000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2451875507561743:ℤ)), (.leaf (2464060801437631:ℤ)), (.leaf (2506003267866356:ℤ)), (.leaf (2519200821027787:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 46 30) 8000 (endpointMeanRuns 46 30) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 46 30, EndpointRunConditions (endpointMeanCutoff 46 30) (endpointMeanBox 46 30).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 30, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 46 30 h) (endpointMeanCornerA 46 30 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 30, endpointJoint24Q (endpointMeanCornerK 46 30 h) (endpointMeanCornerA 46 30 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 46 30, endpointRunWeightQ (endpointMeanCutoff 46 30) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 46 30) = (70943941/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 46 30 h = (logRoundedQ ((endpointMeanCutoff 46 30:ℚ)/200)).2+(70943941/200000000000000:ℚ)+((endpointMeanRuns 46 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 46 30).map (fun r => endpointRunWeightQ (endpointMeanCutoff 46 30) r*endpointJoint24Q (endpointMeanCornerK 46 30 h) (endpointMeanCornerA 46 30 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 46 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 46 30 h≤endpointMeanCorner 46 30 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 46 30 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint46_30

namespace EndpointAnalyticJoint46_31
private noncomputable def weights : IntegerLookupTree := (.leaf (145977208200000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2464060801437631:ℤ)), (.leaf (2494789637406417:ℤ)), (.leaf (2519200821027787:ℤ)), (.leaf (2552499581934158:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 46 31) 8000 (endpointMeanRuns 46 31) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 46 31, EndpointRunConditions (endpointMeanCutoff 46 31) (endpointMeanBox 46 31).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 31, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 46 31 h) (endpointMeanCornerA 46 31 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 31, endpointJoint24Q (endpointMeanCornerK 46 31 h) (endpointMeanCornerA 46 31 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 46 31, endpointRunWeightQ (endpointMeanCutoff 46 31) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 46 31) = (88516253/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 46 31 h = (logRoundedQ ((endpointMeanCutoff 46 31:ℚ)/200)).2+(88516253/250000000000000:ℚ)+((endpointMeanRuns 46 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 46 31).map (fun r => endpointRunWeightQ (endpointMeanCutoff 46 31) r*endpointJoint24Q (endpointMeanCornerK 46 31 h) (endpointMeanCornerA 46 31 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 46 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 46 31 h≤endpointMeanCorner 46 31 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 46 31 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint46_31

namespace EndpointAnalyticJoint46_32
private noncomputable def weights : IntegerLookupTree := (.leaf (141925520800000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2494789637406417:ℤ)), (.leaf (2525901686873605:ℤ)), (.leaf (2552499581934158:ℤ)), (.leaf (2586238485392345:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 46 32) 8000 (endpointMeanRuns 46 32) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 46 32, EndpointRunConditions (endpointMeanCutoff 46 32) (endpointMeanBox 46 32).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 32, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 46 32 h) (endpointMeanCornerA 46 32 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 32, endpointJoint24Q (endpointMeanCornerK 46 32 h) (endpointMeanCornerA 46 32 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 46 32, endpointRunWeightQ (endpointMeanCutoff 46 32) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 46 32) = (352982063/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 46 32 h = (logRoundedQ ((endpointMeanCutoff 46 32:ℚ)/200)).2+(352982063/1000000000000000:ℚ)+((endpointMeanRuns 46 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 46 32).map (fun r => endpointRunWeightQ (endpointMeanCutoff 46 32) r*endpointJoint24Q (endpointMeanCornerK 46 32 h) (endpointMeanCornerA 46 32 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 46 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 46 32 h≤endpointMeanCorner 46 32 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 46 32 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint46_32

namespace EndpointAnalyticJoint46_33
private noncomputable def weights : IntegerLookupTree := (.leaf (137989466100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2525901686873605:ℤ)), (.leaf (2557401728822218:ℤ)), (.leaf (2586238485392345:ℤ)), (.leaf (2620423349200386:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 46 33) 8000 (endpointMeanRuns 46 33) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 46 33, EndpointRunConditions (endpointMeanCutoff 46 33) (endpointMeanBox 46 33).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 33, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 46 33 h) (endpointMeanCornerA 46 33 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 33, endpointJoint24Q (endpointMeanCornerK 46 33 h) (endpointMeanCornerA 46 33 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 46 33, endpointRunWeightQ (endpointMeanCutoff 46 33) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 46 33) = (351909207/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 46 33 h = (logRoundedQ ((endpointMeanCutoff 46 33:ℚ)/200)).2+(351909207/1000000000000000:ℚ)+((endpointMeanRuns 46 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 46 33).map (fun r => endpointRunWeightQ (endpointMeanCutoff 46 33) r*endpointJoint24Q (endpointMeanCornerK 46 33 h) (endpointMeanCornerA 46 33 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 46 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 46 33 h≤endpointMeanCorner 46 33 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 46 33 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint46_33

namespace EndpointAnalyticJoint46_34
private noncomputable def weights : IntegerLookupTree := (.leaf (135681896100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2557401728822218:ℤ)), (.leaf (2567988797923404:ℤ)), (.leaf (2620423349200386:ℤ)), (.leaf (2631918422704995:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 46 34) 8000 (endpointMeanRuns 46 34) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 46 34, EndpointRunConditions (endpointMeanCutoff 46 34) (endpointMeanBox 46 34).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 34, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 46 34 h) (endpointMeanCornerA 46 34 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 34, endpointJoint24Q (endpointMeanCornerK 46 34 h) (endpointMeanCornerA 46 34 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 46 34, endpointRunWeightQ (endpointMeanCutoff 46 34) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 46 34) = (17563513/50000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 46 34 h = (logRoundedQ ((endpointMeanCutoff 46 34:ℚ)/200)).2+(17563513/50000000000000:ℚ)+((endpointMeanRuns 46 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 46 34).map (fun r => endpointRunWeightQ (endpointMeanCutoff 46 34) r*endpointJoint24Q (endpointMeanCornerK 46 34 h) (endpointMeanCornerA 46 34 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 46 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 46 34 h≤endpointMeanCorner 46 34 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 46 34 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint46_34

namespace EndpointAnalyticJoint46_35
private noncomputable def weights : IntegerLookupTree := (.leaf (133789244600000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2567988797923404:ℤ)), (.leaf (2589294601833073:ℤ)), (.leaf (2631918422704995:ℤ)), (.leaf (2655060068055891:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 46 35) 8000 (endpointMeanRuns 46 35) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 46 35, EndpointRunConditions (endpointMeanCutoff 46 35) (endpointMeanBox 46 35).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 35, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 46 35 h) (endpointMeanCornerA 46 35 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 46 35, endpointJoint24Q (endpointMeanCornerK 46 35 h) (endpointMeanCornerA 46 35 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 46 35, endpointRunWeightQ (endpointMeanCutoff 46 35) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 46 35) = (701481/2000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 46 35 h = (logRoundedQ ((endpointMeanCutoff 46 35:ℚ)/200)).2+(701481/2000000000000:ℚ)+((endpointMeanRuns 46 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 46 35).map (fun r => endpointRunWeightQ (endpointMeanCutoff 46 35) r*endpointJoint24Q (endpointMeanCornerK 46 35 h) (endpointMeanCornerA 46 35 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 46 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 46 35 h≤endpointMeanCorner 46 35 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 46 35 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint46_35

namespace EndpointAnalyticJoint47_23
private noncomputable def weights : IntegerLookupTree := (.branch 2374 (.leaf (87461136200000:ℤ)) (.leaf (6966602100000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 123 (.leaf (2313010031309701:ℤ)) (.leaf (3243123027217688:ℤ))), (.branch 123 (.leaf (2328334891755808:ℤ)) (.leaf (3282334489529501:ℤ))), (.branch 123 (.leaf (2358585309028214:ℤ)) (.leaf (3455310616737663:ℤ))), (.branch 123 (.leaf (2375203821584306:ℤ)) (.leaf (3501834160160127:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 47 23) 8000 (endpointMeanRuns 47 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 47 23, EndpointRunConditions (endpointMeanCutoff 47 23) (endpointMeanBox 47 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 47 23 h) (endpointMeanCornerA 47 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 23, endpointJoint24Q (endpointMeanCornerK 47 23 h) (endpointMeanCornerA 47 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 47 23, endpointRunWeightQ (endpointMeanCutoff 47 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 47 23) = (179364019/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 47 23 h = (logRoundedQ ((endpointMeanCutoff 47 23:ℚ)/200)).2+(179364019/500000000000000:ℚ)+((endpointMeanRuns 47 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 47 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 47 23) r*endpointJoint24Q (endpointMeanCornerK 47 23 h) (endpointMeanCornerA 47 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 47 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 47 23 h≤endpointMeanCorner 47 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 47 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint47_23

namespace EndpointAnalyticJoint47_24
private noncomputable def weights : IntegerLookupTree := (.branch 2275 (.leaf (81640426500000:ℤ)) (.leaf (8850981900000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2328334891755808:ℤ)) (.leaf (3376225169382948:ℤ))), (.branch 124 (.leaf (2359110789502181:ℤ)) (.leaf (3461227169954226:ℤ))), (.branch 124 (.leaf (2375203821584306:ℤ)) (.leaf (3623849014407871:ℤ))), (.branch 124 (.leaf (2408598530273440:ℤ)) (.leaf (3726057688744643:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 47 24) 8000 (endpointMeanRuns 47 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 47 24, EndpointRunConditions (endpointMeanCutoff 47 24) (endpointMeanBox 47 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 47 24 h) (endpointMeanCornerA 47 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 24, endpointJoint24Q (endpointMeanCornerK 47 24 h) (endpointMeanCornerA 47 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 47 24, endpointRunWeightQ (endpointMeanCutoff 47 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 47 24) = (178912579/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 47 24 h = (logRoundedQ ((endpointMeanCutoff 47 24:ℚ)/200)).2+(178912579/500000000000000:ℚ)+((endpointMeanRuns 47 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 47 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 47 24) r*endpointJoint24Q (endpointMeanCornerK 47 24 h) (endpointMeanCornerA 47 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 47 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 47 24 h≤endpointMeanCorner 47 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 47 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint47_24

namespace EndpointAnalyticJoint47_25
private noncomputable def weights : IntegerLookupTree := (.branch 2275 (.leaf (81971701600000:ℤ)) (.leaf (8811110400000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 123 (.leaf (2359110789502181:ℤ)) (.leaf (3361720931468339:ℤ))), (.branch 123 (.leaf (2390293482630721:ℤ)) (.leaf (3443027411472704:ℤ))), (.branch 123 (.leaf (2408598530273440:ℤ)) (.leaf (3596215935219292:ℤ))), (.branch 123 (.leaf (2442462759328908:ℤ)) (.leaf (3693141497064433:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 47 25) 8000 (endpointMeanRuns 47 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 47 25, EndpointRunConditions (endpointMeanCutoff 47 25) (endpointMeanBox 47 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 47 25 h) (endpointMeanCornerA 47 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 25, endpointJoint24Q (endpointMeanCornerK 47 25 h) (endpointMeanCornerA 47 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 47 25, endpointRunWeightQ (endpointMeanCutoff 47 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 47 25) = (89204453/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 47 25 h = (logRoundedQ ((endpointMeanCutoff 47 25:ℚ)/200)).2+(89204453/250000000000000:ℚ)+((endpointMeanRuns 47 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 47 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 47 25) r*endpointJoint24Q (endpointMeanCornerK 47 25 h) (endpointMeanCornerA 47 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 47 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 47 25 h≤endpointMeanCorner 47 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 47 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint47_25

namespace EndpointAnalyticJoint47_26
private noncomputable def weights : IntegerLookupTree := (.branch 2874 (.leaf (94053351800000:ℤ)) (.leaf (1985009300000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 119 (.leaf (2390293482630721:ℤ)) (.leaf (3092511408242233:ℤ))), (.branch 119 (.leaf (2421888348157046:ℤ)) (.leaf (3156681576343463:ℤ))), (.branch 119 (.leaf (2442462759328908:ℤ)) (.leaf (3253180914473737:ℤ))), (.branch 119 (.leaf (2476803110077182:ℤ)) (.leaf (3327160226196845:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 47 26) 8000 (endpointMeanRuns 47 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 47 26, EndpointRunConditions (endpointMeanCutoff 47 26) (endpointMeanBox 47 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 47 26 h) (endpointMeanCornerA 47 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 26, endpointJoint24Q (endpointMeanCornerK 47 26 h) (endpointMeanCornerA 47 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 47 26, endpointRunWeightQ (endpointMeanCutoff 47 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 47 26) = (17785439/50000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 47 26 h = (logRoundedQ ((endpointMeanCutoff 47 26:ℚ)/200)).2+(17785439/50000000000000:ℚ)+((endpointMeanRuns 47 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 47 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 47 26) r*endpointJoint24Q (endpointMeanCornerK 47 26 h) (endpointMeanCornerA 47 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 47 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 47 26 h≤endpointMeanCorner 47 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 47 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint47_26

namespace EndpointAnalyticJoint47_27
private noncomputable def weights : IntegerLookupTree := (.leaf (148047524300000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2421888348157046:ℤ)), (.leaf (2453900834170094:ℤ)), (.leaf (2476803110077182:ℤ)), (.leaf (2511626276657553:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 47 27) 8000 (endpointMeanRuns 47 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 47 27, EndpointRunConditions (endpointMeanCutoff 47 27) (endpointMeanBox 47 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 47 27 h) (endpointMeanCornerA 47 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 27, endpointJoint24Q (endpointMeanCornerK 47 27 h) (endpointMeanCornerA 47 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 47 27, endpointRunWeightQ (endpointMeanCutoff 47 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 47 27) = (354610331/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 47 27 h = (logRoundedQ ((endpointMeanCutoff 47 27:ℚ)/200)).2+(354610331/1000000000000000:ℚ)+((endpointMeanRuns 47 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 47 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 47 27) r*endpointJoint24Q (endpointMeanCornerK 47 27 h) (endpointMeanCornerA 47 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 47 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 47 27 h≤endpointMeanCorner 47 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 47 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint47_27

namespace EndpointAnalyticJoint47_28
private noncomputable def weights : IntegerLookupTree := (.leaf (144342431700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2453900834170094:ℤ)), (.leaf (2486336460771566:ℤ)), (.leaf (2511626276657553:ℤ)), (.leaf (2546939047327066:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 47 28) 8000 (endpointMeanRuns 47 28) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 47 28, EndpointRunConditions (endpointMeanCutoff 47 28) (endpointMeanBox 47 28).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 28, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 47 28 h) (endpointMeanCornerA 47 28 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 28, endpointJoint24Q (endpointMeanCornerK 47 28 h) (endpointMeanCornerA 47 28 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 47 28, endpointRunWeightQ (endpointMeanCutoff 47 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 47 28) = (353630609/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 47 28 h = (logRoundedQ ((endpointMeanCutoff 47 28:ℚ)/200)).2+(353630609/1000000000000000:ℚ)+((endpointMeanRuns 47 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 47 28).map (fun r => endpointRunWeightQ (endpointMeanCutoff 47 28) r*endpointJoint24Q (endpointMeanCornerK 47 28 h) (endpointMeanCornerA 47 28 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 47 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 47 28 h≤endpointMeanCorner 47 28 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 47 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint47_28

namespace EndpointAnalyticJoint47_29
private noncomputable def weights : IntegerLookupTree := (.leaf (141129171400000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2486336460771566:ℤ)), (.leaf (2506003267866356:ℤ)), (.leaf (2546939047327066:ℤ)), (.leaf (2568364579299543:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 47 29) 8000 (endpointMeanRuns 47 29) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 47 29, EndpointRunConditions (endpointMeanCutoff 47 29) (endpointMeanBox 47 29).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 29, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 47 29 h) (endpointMeanCornerA 47 29 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 29, endpointJoint24Q (endpointMeanCornerK 47 29 h) (endpointMeanCornerA 47 29 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 47 29, endpointRunWeightQ (endpointMeanCutoff 47 29) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 47 29) = (35276669/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 47 29 h = (logRoundedQ ((endpointMeanCutoff 47 29:ℚ)/200)).2+(35276669/100000000000000:ℚ)+((endpointMeanRuns 47 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 47 29).map (fun r => endpointRunWeightQ (endpointMeanCutoff 47 29) r*endpointJoint24Q (endpointMeanCornerK 47 29 h) (endpointMeanCornerA 47 29 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 47 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 47 29 h≤endpointMeanCorner 47 29 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 47 29 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint47_29

namespace EndpointAnalyticJoint47_30
private noncomputable def weights : IntegerLookupTree := (.leaf (139158348700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2506003267866356:ℤ)), (.leaf (2519200821027787:ℤ)), (.leaf (2568364579299543:ℤ)), (.leaf (2582748305783772:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 47 30) 8000 (endpointMeanRuns 47 30) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 47 30, EndpointRunConditions (endpointMeanCutoff 47 30) (endpointMeanBox 47 30).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 30, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 47 30 h) (endpointMeanCornerA 47 30 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 30, endpointJoint24Q (endpointMeanCornerK 47 30 h) (endpointMeanCornerA 47 30 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 47 30, endpointRunWeightQ (endpointMeanCutoff 47 30) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 47 30) = (70446003/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 47 30 h = (logRoundedQ ((endpointMeanCutoff 47 30:ℚ)/200)).2+(70446003/200000000000000:ℚ)+((endpointMeanRuns 47 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 47 30).map (fun r => endpointRunWeightQ (endpointMeanCutoff 47 30) r*endpointJoint24Q (endpointMeanCornerK 47 30 h) (endpointMeanCornerA 47 30 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 47 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 47 30 h≤endpointMeanCorner 47 30 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 47 30 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint47_30

namespace EndpointAnalyticJoint47_31
private noncomputable def weights : IntegerLookupTree := (.leaf (136446644300000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2519200821027787:ℤ)), (.leaf (2552499581934158:ℤ)), (.leaf (2582748305783772:ℤ)), (.leaf (2619061032508619:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 47 31) 8000 (endpointMeanRuns 47 31) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 47 31, EndpointRunConditions (endpointMeanCutoff 47 31) (endpointMeanBox 47 31).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 31, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 47 31 h) (endpointMeanCornerA 47 31 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 31, endpointJoint24Q (endpointMeanCornerK 47 31 h) (endpointMeanCornerA 47 31 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 47 31, endpointRunWeightQ (endpointMeanCutoff 47 31) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 47 31) = (351482849/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 47 31 h = (logRoundedQ ((endpointMeanCutoff 47 31:ℚ)/200)).2+(351482849/1000000000000000:ℚ)+((endpointMeanRuns 47 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 47 31).map (fun r => endpointRunWeightQ (endpointMeanCutoff 47 31) r*endpointJoint24Q (endpointMeanCornerK 47 31 h) (endpointMeanCornerA 47 31 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 47 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 47 31 h≤endpointMeanCorner 47 31 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 47 31 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint47_31

namespace EndpointAnalyticJoint47_32
private noncomputable def weights : IntegerLookupTree := (.leaf (133039802200000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2552499581934158:ℤ)), (.leaf (2586238485392345:ℤ)), (.leaf (2619061032508619:ℤ)), (.leaf (2655884306126184:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 47 32) 8000 (endpointMeanRuns 47 32) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 47 32, EndpointRunConditions (endpointMeanCutoff 47 32) (endpointMeanBox 47 32).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 32, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 47 32 h) (endpointMeanCornerA 47 32 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 32, endpointJoint24Q (endpointMeanCornerK 47 32 h) (endpointMeanCornerA 47 32 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 47 32, endpointRunWeightQ (endpointMeanCutoff 47 32) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 47 32) = (350529277/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 47 32 h = (logRoundedQ ((endpointMeanCutoff 47 32:ℚ)/200)).2+(350529277/1000000000000000:ℚ)+((endpointMeanRuns 47 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 47 32).map (fun r => endpointRunWeightQ (endpointMeanCutoff 47 32) r*endpointJoint24Q (endpointMeanCornerK 47 32 h) (endpointMeanCornerA 47 32 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 47 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 47 32 h≤endpointMeanCorner 47 32 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 47 32 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint47_32

namespace EndpointAnalyticJoint47_33
private noncomputable def weights : IntegerLookupTree := (.leaf (129356782800000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2586238485392345:ℤ)), (.leaf (2620423349200386:ℤ)), (.leaf (2655884306126184:ℤ)), (.leaf (2693225304784549:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 47 33) 8000 (endpointMeanRuns 47 33) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 47 33, EndpointRunConditions (endpointMeanCutoff 47 33) (endpointMeanBox 47 33).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 33, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 47 33 h) (endpointMeanCornerA 47 33 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 33, endpointJoint24Q (endpointMeanCornerK 47 33 h) (endpointMeanCornerA 47 33 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 47 33, endpointRunWeightQ (endpointMeanCutoff 47 33) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 47 33) = (43684867/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 47 33 h = (logRoundedQ ((endpointMeanCutoff 47 33:ℚ)/200)).2+(43684867/125000000000000:ℚ)+((endpointMeanRuns 47 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 47 33).map (fun r => endpointRunWeightQ (endpointMeanCutoff 47 33) r*endpointJoint24Q (endpointMeanCornerK 47 33 h) (endpointMeanCornerA 47 33 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 47 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 47 33 h≤endpointMeanCorner 47 33 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 47 33 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint47_33

namespace EndpointAnalyticJoint47_34
private noncomputable def weights : IntegerLookupTree := (.leaf (126841124900000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2620423349200386:ℤ)), (.leaf (2631918422704995:ℤ)), (.leaf (2693225304784549:ℤ)), (.leaf (2705788609523035:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 47 34) 8000 (endpointMeanRuns 47 34) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 47 34, EndpointRunConditions (endpointMeanCutoff 47 34) (endpointMeanBox 47 34).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 34, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 47 34 h) (endpointMeanCornerA 47 34 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 34, endpointJoint24Q (endpointMeanCornerK 47 34 h) (endpointMeanCornerA 47 34 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 47 34, endpointRunWeightQ (endpointMeanCutoff 47 34) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 47 34) = (174374679/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 47 34 h = (logRoundedQ ((endpointMeanCutoff 47 34:ℚ)/200)).2+(174374679/500000000000000:ℚ)+((endpointMeanRuns 47 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 47 34).map (fun r => endpointRunWeightQ (endpointMeanCutoff 47 34) r*endpointJoint24Q (endpointMeanCornerK 47 34 h) (endpointMeanCornerA 47 34 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 47 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 47 34 h≤endpointMeanCorner 47 34 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 47 34 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint47_34

namespace EndpointAnalyticJoint47_35
private noncomputable def weights : IntegerLookupTree := (.leaf (125426216700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2631918422704995:ℤ)), (.leaf (2655060068055891:ℤ)), (.leaf (2705788609523035:ℤ)), (.leaf (2731091307554576:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 47 35) 8000 (endpointMeanRuns 47 35) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 47 35, EndpointRunConditions (endpointMeanCutoff 47 35) (endpointMeanBox 47 35).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 35, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 47 35 h) (endpointMeanCornerA 47 35 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 35, endpointJoint24Q (endpointMeanCornerK 47 35 h) (endpointMeanCornerA 47 35 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 47 35, endpointRunWeightQ (endpointMeanCutoff 47 35) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 47 35) = (348334523/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 47 35 h = (logRoundedQ ((endpointMeanCutoff 47 35:ℚ)/200)).2+(348334523/1000000000000000:ℚ)+((endpointMeanRuns 47 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 47 35).map (fun r => endpointRunWeightQ (endpointMeanCutoff 47 35) r*endpointJoint24Q (endpointMeanCornerK 47 35 h) (endpointMeanCornerA 47 35 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 47 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 47 35 h≤endpointMeanCorner 47 35 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 47 35 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint47_35

namespace EndpointAnalyticJoint47_36
private noncomputable def weights : IntegerLookupTree := (.leaf (122301605000000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2655060068055891:ℤ)), (.leaf (2690154614572503:ℤ)), (.leaf (2731091307554576:ℤ)), (.leaf (2769489695848837:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 47 36) 8000 (endpointMeanRuns 47 36) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 47 36, EndpointRunConditions (endpointMeanCutoff 47 36) (endpointMeanBox 47 36).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 36, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 47 36 h) (endpointMeanCornerA 47 36 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 47 36, endpointJoint24Q (endpointMeanCornerK 47 36 h) (endpointMeanCornerA 47 36 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 47 36, endpointRunWeightQ (endpointMeanCutoff 47 36) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 47 36) = (173703287/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 47 36 h = (logRoundedQ ((endpointMeanCutoff 47 36:ℚ)/200)).2+(173703287/500000000000000:ℚ)+((endpointMeanRuns 47 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 47 36).map (fun r => endpointRunWeightQ (endpointMeanCutoff 47 36) r*endpointJoint24Q (endpointMeanCornerK 47 36 h) (endpointMeanCornerA 47 36 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 47 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 47 36 h≤endpointMeanCorner 47 36 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 47 36 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint47_36

private theorem activeIndices42 : ∀ai : Fin 42, endpointMeanActive 42 ai → ai∈
    ([18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow42 (ai : Fin 42) : endpointMeanActive 42 ai →
    EndpointJointNumericalConditions 42 ai := by
  intro hact
  have hi := activeIndices42 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint42_18.conditions
  · exact EndpointAnalyticJoint42_19.conditions
  · exact EndpointAnalyticJoint42_20.conditions
  · exact EndpointAnalyticJoint42_21.conditions
  · exact EndpointAnalyticJoint42_22.conditions
  · exact EndpointAnalyticJoint42_23.conditions
  · exact EndpointAnalyticJoint42_24.conditions
  · exact EndpointAnalyticJoint42_25.conditions
  · exact EndpointAnalyticJoint42_26.conditions
  · exact EndpointAnalyticJoint42_27.conditions
  · exact EndpointAnalyticJoint42_28.conditions
  · exact EndpointAnalyticJoint42_29.conditions
  · exact EndpointAnalyticJoint42_30.conditions
  · exact EndpointAnalyticJoint42_31.conditions
  · exact EndpointAnalyticJoint42_32.conditions

private theorem activeIndices43 : ∀ai : Fin 42, endpointMeanActive 43 ai → ai∈
    ([19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow43 (ai : Fin 42) : endpointMeanActive 43 ai →
    EndpointJointNumericalConditions 43 ai := by
  intro hact
  have hi := activeIndices43 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint43_19.conditions
  · exact EndpointAnalyticJoint43_20.conditions
  · exact EndpointAnalyticJoint43_21.conditions
  · exact EndpointAnalyticJoint43_22.conditions
  · exact EndpointAnalyticJoint43_23.conditions
  · exact EndpointAnalyticJoint43_24.conditions
  · exact EndpointAnalyticJoint43_25.conditions
  · exact EndpointAnalyticJoint43_26.conditions
  · exact EndpointAnalyticJoint43_27.conditions
  · exact EndpointAnalyticJoint43_28.conditions
  · exact EndpointAnalyticJoint43_29.conditions
  · exact EndpointAnalyticJoint43_30.conditions
  · exact EndpointAnalyticJoint43_31.conditions
  · exact EndpointAnalyticJoint43_32.conditions
  · exact EndpointAnalyticJoint43_33.conditions

private theorem activeIndices44 : ∀ai : Fin 42, endpointMeanActive 44 ai → ai∈
    ([20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow44 (ai : Fin 42) : endpointMeanActive 44 ai →
    EndpointJointNumericalConditions 44 ai := by
  intro hact
  have hi := activeIndices44 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint44_20.conditions
  · exact EndpointAnalyticJoint44_21.conditions
  · exact EndpointAnalyticJoint44_22.conditions
  · exact EndpointAnalyticJoint44_23.conditions
  · exact EndpointAnalyticJoint44_24.conditions
  · exact EndpointAnalyticJoint44_25.conditions
  · exact EndpointAnalyticJoint44_26.conditions
  · exact EndpointAnalyticJoint44_27.conditions
  · exact EndpointAnalyticJoint44_28.conditions
  · exact EndpointAnalyticJoint44_29.conditions
  · exact EndpointAnalyticJoint44_30.conditions
  · exact EndpointAnalyticJoint44_31.conditions
  · exact EndpointAnalyticJoint44_32.conditions
  · exact EndpointAnalyticJoint44_33.conditions

private theorem activeIndices45 : ∀ai : Fin 42, endpointMeanActive 45 ai → ai∈
    ([21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow45 (ai : Fin 42) : endpointMeanActive 45 ai →
    EndpointJointNumericalConditions 45 ai := by
  intro hact
  have hi := activeIndices45 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint45_21.conditions
  · exact EndpointAnalyticJoint45_22.conditions
  · exact EndpointAnalyticJoint45_23.conditions
  · exact EndpointAnalyticJoint45_24.conditions
  · exact EndpointAnalyticJoint45_25.conditions
  · exact EndpointAnalyticJoint45_26.conditions
  · exact EndpointAnalyticJoint45_27.conditions
  · exact EndpointAnalyticJoint45_28.conditions
  · exact EndpointAnalyticJoint45_29.conditions
  · exact EndpointAnalyticJoint45_30.conditions
  · exact EndpointAnalyticJoint45_31.conditions
  · exact EndpointAnalyticJoint45_32.conditions
  · exact EndpointAnalyticJoint45_33.conditions
  · exact EndpointAnalyticJoint45_34.conditions

private theorem activeIndices46 : ∀ai : Fin 42, endpointMeanActive 46 ai → ai∈
    ([22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow46 (ai : Fin 42) : endpointMeanActive 46 ai →
    EndpointJointNumericalConditions 46 ai := by
  intro hact
  have hi := activeIndices46 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint46_22.conditions
  · exact EndpointAnalyticJoint46_23.conditions
  · exact EndpointAnalyticJoint46_24.conditions
  · exact EndpointAnalyticJoint46_25.conditions
  · exact EndpointAnalyticJoint46_26.conditions
  · exact EndpointAnalyticJoint46_27.conditions
  · exact EndpointAnalyticJoint46_28.conditions
  · exact EndpointAnalyticJoint46_29.conditions
  · exact EndpointAnalyticJoint46_30.conditions
  · exact EndpointAnalyticJoint46_31.conditions
  · exact EndpointAnalyticJoint46_32.conditions
  · exact EndpointAnalyticJoint46_33.conditions
  · exact EndpointAnalyticJoint46_34.conditions
  · exact EndpointAnalyticJoint46_35.conditions

private theorem activeIndices47 : ∀ai : Fin 42, endpointMeanActive 47 ai → ai∈
    ([23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow47 (ai : Fin 42) : endpointMeanActive 47 ai →
    EndpointJointNumericalConditions 47 ai := by
  intro hact
  have hi := activeIndices47 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint47_23.conditions
  · exact EndpointAnalyticJoint47_24.conditions
  · exact EndpointAnalyticJoint47_25.conditions
  · exact EndpointAnalyticJoint47_26.conditions
  · exact EndpointAnalyticJoint47_27.conditions
  · exact EndpointAnalyticJoint47_28.conditions
  · exact EndpointAnalyticJoint47_29.conditions
  · exact EndpointAnalyticJoint47_30.conditions
  · exact EndpointAnalyticJoint47_31.conditions
  · exact EndpointAnalyticJoint47_32.conditions
  · exact EndpointAnalyticJoint47_33.conditions
  · exact EndpointAnalyticJoint47_34.conditions
  · exact EndpointAnalyticJoint47_35.conditions
  · exact EndpointAnalyticJoint47_36.conditions

end SingularValueBounds.KL.Certificates
