import SingularValueBounds.KL.Certificates.EndpointAnalyticLogs
import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SingularValueBounds.KL.Certificates

namespace EndpointAnalyticJoint36_13
private noncomputable def weights : IntegerLookupTree := (.branch 1481 (.leaf (129865258500000:ℤ)) (.branch 2605 (.leaf (29047433200000:ℤ)) (.leaf (3983511100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (1919492737277062:ℤ)) (.branch 144 (.leaf (2209507665886213:ℤ)) (.leaf (2660749755542834:ℤ)))), (.branch 125 (.leaf (1923887560405261:ℤ)) (.branch 144 (.leaf (2217085702444840:ℤ)) (.leaf (2674829551490096:ℤ)))), (.branch 125 (.leaf (1928665780165269:ℤ)) (.branch 144 (.leaf (2228734497737883:ℤ)) (.leaf (2707442238197024:ℤ)))), (.branch 125 (.leaf (1933269696020096:ℤ)) (.branch 144 (.leaf (2236773950536138:ℤ)) (.leaf (2722735593556670:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 36 13) 8000 (endpointMeanRuns 36 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 36 13, EndpointRunConditions (endpointMeanCutoff 36 13) (endpointMeanBox 36 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 36 13 h) (endpointMeanCornerA 36 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 13, endpointJoint24Q (endpointMeanCornerK 36 13 h) (endpointMeanCornerA 36 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 36 13, endpointRunWeightQ (endpointMeanCutoff 36 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 36 13) = (100198799/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 36 13 h = (logRoundedQ ((endpointMeanCutoff 36 13:ℚ)/200)).2+(100198799/250000000000000:ℚ)+((endpointMeanRuns 36 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 36 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 36 13) r*endpointJoint24Q (endpointMeanCornerK 36 13 h) (endpointMeanCornerA 36 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 36 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 36 13 h≤endpointMeanCorner 36 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 36 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint36_13

namespace EndpointAnalyticJoint36_14
private noncomputable def weights : IntegerLookupTree := (.branch 1253 (.leaf (94207214400000:ℤ)) (.branch 2605 (.leaf (55725347800000:ℤ)) (.leaf (3971938900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (1923887560405261:ℤ)) (.branch 152 (.leaf (2217085702444840:ℤ)) (.leaf (2935241277522679:ℤ)))), (.branch 125 (.leaf (1939665659686201:ℤ)) (.branch 152 (.leaf (2244362912228014:ℤ)) (.leaf (3002416575366101:ℤ)))), (.branch 125 (.leaf (1933269696020096:ℤ)) (.branch 152 (.leaf (2236773950536138:ℤ)) (.leaf (3007717805216678:ℤ)))), (.branch 125 (.leaf (1949802150683548:ℤ)) (.branch 152 (.leaf (2265723747809298:ℤ)) (.leaf (3081916674281939:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 36 14) 8000 (endpointMeanRuns 36 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 36 14, EndpointRunConditions (endpointMeanCutoff 36 14) (endpointMeanBox 36 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 36 14 h) (endpointMeanCornerA 36 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 14, endpointJoint24Q (endpointMeanCornerK 36 14 h) (endpointMeanCornerA 36 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 36 14, endpointRunWeightQ (endpointMeanCutoff 36 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 36 14) = (24998853/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 36 14 h = (logRoundedQ ((endpointMeanCutoff 36 14:ℚ)/200)).2+(24998853/62500000000000:ℚ)+((endpointMeanRuns 36 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 36 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 36 14) r*endpointJoint24Q (endpointMeanCornerK 36 14 h) (endpointMeanCornerA 36 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 36 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 36 14 h≤endpointMeanCorner 36 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 36 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint36_14

namespace EndpointAnalyticJoint36_15
private noncomputable def weights : IntegerLookupTree := (.branch 1386 (.leaf (110211800600000:ℤ)) (.branch 2605 (.leaf (37926260100000:ℤ)) (.leaf (3953592000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (1939665659686201:ℤ)) (.branch 147 (.leaf (2244362912228014:ℤ)) (.leaf (2822714945466798:ℤ)))), (.branch 125 (.leaf (1955573157598354:ℤ)) (.branch 147 (.leaf (2271975718498380:ℤ)) (.leaf (2880255809619539:ℤ)))), (.branch 125 (.leaf (1949802150683548:ℤ)) (.branch 147 (.leaf (2265723747809298:ℤ)) (.leaf (2883700054151960:ℤ)))), (.branch 125 (.leaf (1966475983478444:ℤ)) (.branch 147 (.leaf (2295048232369015:ℤ)) (.leaf (2946680132937871:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 36 15) 8000 (endpointMeanRuns 36 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 36 15, EndpointRunConditions (endpointMeanCutoff 36 15) (endpointMeanBox 36 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 36 15 h) (endpointMeanCornerA 36 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 15, endpointJoint24Q (endpointMeanCornerK 36 15 h) (endpointMeanCornerA 36 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 36 15, endpointRunWeightQ (endpointMeanCutoff 36 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 36 15) = (99672953/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 36 15 h = (logRoundedQ ((endpointMeanCutoff 36 15:ℚ)/200)).2+(99672953/250000000000000:ℚ)+((endpointMeanRuns 36 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 36 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 36 15) r*endpointJoint24Q (endpointMeanCornerK 36 15 h) (endpointMeanCornerA 36 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 36 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 36 15 h≤endpointMeanCorner 36 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 36 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint36_15

namespace EndpointAnalyticJoint36_16
private noncomputable def weights : IntegerLookupTree := (.branch 1386 (.leaf (105960572500000:ℤ)) (.branch 2605 (.leaf (37669151600000:ℤ)) (.leaf (3933194400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (1955573157598354:ℤ)) (.branch 147 (.leaf (2271975718498380:ℤ)) (.leaf (2880255809619539:ℤ)))), (.branch 125 (.leaf (1971611115359896:ℤ)) (.branch 147 (.leaf (2299928250160740:ℤ)) (.leaf (2938969640618533:ℤ)))), (.branch 125 (.leaf (1966475983478444:ℤ)) (.branch 147 (.leaf (2295048232369015:ℤ)) (.leaf (2946680132937871:ℤ)))), (.branch 125 (.leaf (1983292403407101:ℤ)) (.branch 147 (.leaf (2324752253664182:ℤ)) (.leaf (3011035698164602:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 36 16) 8000 (endpointMeanRuns 36 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 36 16, EndpointRunConditions (endpointMeanCutoff 36 16) (endpointMeanBox 36 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 36 16 h) (endpointMeanCornerA 36 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 16, endpointJoint24Q (endpointMeanCornerK 36 16 h) (endpointMeanCornerA 36 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 36 16, endpointRunWeightQ (endpointMeanCutoff 36 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 36 16) = (79451563/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 36 16 h = (logRoundedQ ((endpointMeanCutoff 36 16:ℚ)/200)).2+(79451563/200000000000000:ℚ)+((endpointMeanRuns 36 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 36 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 36 16) r*endpointJoint24Q (endpointMeanCornerK 36 16 h) (endpointMeanCornerA 36 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 36 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 36 16 h≤endpointMeanCorner 36 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 36 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint36_16

namespace EndpointAnalyticJoint36_17
private noncomputable def weights : IntegerLookupTree := (.branch 1386 (.leaf (102311738600000:ℤ)) (.branch 2605 (.leaf (37443268900000:ℤ)) (.leaf (3915274100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (1971611115359896:ℤ)) (.branch 147 (.leaf (2299928250160740:ℤ)) (.leaf (2938969640618533:ℤ)))), (.branch 125 (.leaf (1987780602892213:ℤ)) (.branch 147 (.leaf (2328224686918552:ℤ)) (.leaf (2998880349318127:ℤ)))), (.branch 125 (.leaf (1983292403407101:ℤ)) (.branch 147 (.leaf (2324752253664182:ℤ)) (.leaf (3011035698164602:ℤ)))), (.branch 125 (.leaf (2000252629810687:ℤ)) (.branch 147 (.leaf (2354840723908469:ℤ)) (.leaf (3076796790489226:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 36 17) 8000 (endpointMeanRuns 36 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 36 17, EndpointRunConditions (endpointMeanCutoff 36 17) (endpointMeanBox 36 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 36 17 h) (endpointMeanCornerA 36 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 17, endpointJoint24Q (endpointMeanCornerK 36 17 h) (endpointMeanCornerA 36 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 36 17, endpointRunWeightQ (endpointMeanCutoff 36 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 36 17) = (49499747/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 36 17 h = (logRoundedQ ((endpointMeanCutoff 36 17:ℚ)/200)).2+(49499747/125000000000000:ℚ)+((endpointMeanRuns 36 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 36 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 36 17) r*endpointJoint24Q (endpointMeanCornerK 36 17 h) (endpointMeanCornerA 36 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 36 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 36 17 h≤endpointMeanCorner 36 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 36 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint36_17

namespace EndpointAnalyticJoint36_18
private noncomputable def weights : IntegerLookupTree := (.branch 1386 (.branch 1143 (.leaf (64171937000000:ℤ)) (.leaf (18315122900000:ℤ))) (.branch 2605 (.leaf (37219831500000:ℤ)) (.leaf (3897547800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 147 (.branch 125 (.leaf (1987780602892213:ℤ)) (.leaf (2328224686918552:ℤ))) (.branch 157 (.leaf (2998880349318127:ℤ)) (.leaf (3464044656553855:ℤ)))), (.branch 147 (.branch 125 (.leaf (2004082698891295:ℤ)) (.leaf (2356869259898932:ℤ))) (.branch 157 (.leaf (3060012333993935:ℤ)) (.leaf (3553205103971282:ℤ)))), (.branch 147 (.branch 125 (.leaf (2000252629810687:ℤ)) (.leaf (2354840723908469:ℤ))) (.branch 157 (.leaf (3076796790489226:ℤ)) (.leaf (3600843572228463:ℤ)))), (.branch 147 (.branch 125 (.leaf (2017357892457629:ℤ)) (.leaf (2385318618892623:ℤ))) (.branch 157 (.leaf (3143994106657478:ℤ)) (.leaf (3701481113509032:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 36 18) 8000 (endpointMeanRuns 36 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 36 18, EndpointRunConditions (endpointMeanCutoff 36 18) (endpointMeanBox 36 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 36 18 h) (endpointMeanCornerA 36 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 18, endpointJoint24Q (endpointMeanCornerK 36 18 h) (endpointMeanCornerA 36 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 36 18, endpointRunWeightQ (endpointMeanCutoff 36 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 36 18) = (12335993/31250000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 36 18 h = (logRoundedQ ((endpointMeanCutoff 36 18:ℚ)/200)).2+(12335993/31250000000000:ℚ)+((endpointMeanRuns 36 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 36 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 36 18) r*endpointJoint24Q (endpointMeanCornerK 36 18 h) (endpointMeanCornerA 36 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 36 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 36 18 h≤endpointMeanCorner 36 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 36 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint36_18

namespace EndpointAnalyticJoint36_19
private noncomputable def weights : IntegerLookupTree := (.branch 1629 (.branch 1253 (.leaf (77071238200000:ℤ)) (.leaf (21153763200000:ℤ))) (.branch 2605 (.leaf (18064291800000:ℤ)) (.leaf (3877832400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 140 (.branch 125 (.leaf (2004082698891295:ℤ)) (.leaf (2356869259898932:ℤ))) (.branch 152 (.leaf (2792879147768096:ℤ)) (.leaf (3286847241499618:ℤ)))), (.branch 140 (.branch 125 (.leaf (2020518490899671:ℤ)) (.leaf (2385866252285322:ℤ))) (.branch 152 (.leaf (2841372998777331:ℤ)) (.leaf (3362069317485115:ℤ)))), (.branch 140 (.branch 125 (.leaf (2017357892457629:ℤ)) (.leaf (2385318618892623:ℤ))) (.branch 152 (.leaf (2851274963260060:ℤ)) (.leaf (3397473793993588:ℤ)))), (.branch 140 (.branch 125 (.leaf (2034609431632777:ℤ)) (.leaf (2416190978807351:ℤ))) (.branch 152 (.leaf (2903943778072037:ℤ)) (.leaf (3481287745141518:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 36 19) 8000 (endpointMeanRuns 36 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 36 19, EndpointRunConditions (endpointMeanCutoff 36 19) (endpointMeanBox 36 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 36 19 h) (endpointMeanCornerA 36 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 19, endpointJoint24Q (endpointMeanCornerK 36 19 h) (endpointMeanCornerA 36 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 36 19, endpointRunWeightQ (endpointMeanCutoff 36 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 36 19) = (19668287/50000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 36 19 h = (logRoundedQ ((endpointMeanCutoff 36 19:ℚ)/200)).2+(19668287/50000000000000:ℚ)+((endpointMeanRuns 36 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 36 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 36 19) r*endpointJoint24Q (endpointMeanCornerK 36 19 h) (endpointMeanCornerA 36 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 36 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 36 19 h≤endpointMeanCorner 36 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 36 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint36_19

namespace EndpointAnalyticJoint36_20
private noncomputable def weights : IntegerLookupTree := (.branch 1386 (.leaf (91652380100000:ℤ)) (.branch 2605 (.leaf (36752909300000:ℤ)) (.leaf (3860504700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2020518490899671:ℤ)) (.branch 147 (.leaf (2385866252285322:ℤ)) (.leaf (3122390490278836:ℤ)))), (.branch 125 (.leaf (2037089075378983:ℤ)) (.branch 147 (.leaf (2415219999957960:ℤ)) (.leaf (3186040221301621:ℤ)))), (.branch 125 (.leaf (2034609431632777:ℤ)) (.branch 147 (.leaf (2416190978807351:ℤ)) (.leaf (3212659013832762:ℤ)))), (.branch 125 (.leaf (2052008498227335:ℤ)) (.branch 147 (.leaf (2447462909076812:ℤ)) (.leaf (3282823564238117:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 36 20) 8000 (endpointMeanRuns 36 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 36 20, EndpointRunConditions (endpointMeanCutoff 36 20) (endpointMeanBox 36 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 36 20 h) (endpointMeanCornerA 36 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 20, endpointJoint24Q (endpointMeanCornerK 36 20 h) (endpointMeanCornerA 36 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 36 20, endpointRunWeightQ (endpointMeanCutoff 36 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 36 20) = (98036891/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 36 20 h = (logRoundedQ ((endpointMeanCutoff 36 20:ℚ)/200)).2+(98036891/250000000000000:ℚ)+((endpointMeanRuns 36 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 36 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 36 20) r*endpointJoint24Q (endpointMeanCornerK 36 20 h) (endpointMeanCornerA 36 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 36 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 36 20 h≤endpointMeanCorner 36 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 36 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint36_20

namespace EndpointAnalyticJoint36_21
private noncomputable def weights : IntegerLookupTree := (.branch 1386 (.leaf (88465787700000:ℤ)) (.branch 2605 (.leaf (36536783500000:ℤ)) (.leaf (3843358500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2037089075378983:ℤ)) (.branch 147 (.leaf (2415219999957960:ℤ)) (.leaf (3186040221301621:ℤ)))), (.branch 125 (.leaf (2053795557783124:ℤ)) (.branch 147 (.leaf (2444934892142196:ℤ)) (.leaf (3250987448032220:ℤ)))), (.branch 125 (.leaf (2052008498227335:ℤ)) (.branch 147 (.leaf (2447462909076812:ℤ)) (.leaf (3282823564238117:ℤ)))), (.branch 125 (.leaf (2069556353829584:ℤ)) (.branch 147 (.leaf (2479139581202922:ℤ)) (.leaf (3354520510117866:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 36 21) 8000 (endpointMeanRuns 36 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 36 21, EndpointRunConditions (endpointMeanCutoff 36 21) (endpointMeanBox 36 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 36 21 h) (endpointMeanCornerA 36 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 21, endpointJoint24Q (endpointMeanCornerK 36 21 h) (endpointMeanCornerA 36 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 36 21, endpointRunWeightQ (endpointMeanCutoff 36 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 36 21) = (390942143/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 36 21 h = (logRoundedQ ((endpointMeanCutoff 36 21:ℚ)/200)).2+(390942143/1000000000000000:ℚ)+((endpointMeanRuns 36 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 36 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 36 21) r*endpointJoint24Q (endpointMeanCornerK 36 21 h) (endpointMeanCornerA 36 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 36 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 36 21 h≤endpointMeanCorner 36 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 36 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint36_21

namespace EndpointAnalyticJoint36_22
private noncomputable def weights : IntegerLookupTree := (.branch 1386 (.leaf (85003391000000:ℤ)) (.branch 2605 (.leaf (36296316700000:ℤ)) (.leaf (3824281100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2053795557783124:ℤ)) (.branch 147 (.leaf (2444934892142196:ℤ)) (.leaf (3250987448032220:ℤ)))), (.branch 125 (.leaf (2070639052631978:ℤ)) (.branch 147 (.leaf (2475015372064837:ℤ)) (.leaf (3317258619837901:ℤ)))), (.branch 125 (.leaf (2069556353829584:ℤ)) (.branch 147 (.leaf (2479139581202922:ℤ)) (.leaf (3354520510117866:ℤ)))), (.branch 125 (.leaf (2087254270816324:ℤ)) (.branch 147 (.leaf (2511226233620565:ℤ)) (.leaf (3427783319026157:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 36 22) 8000 (endpointMeanRuns 36 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 36 22, EndpointRunConditions (endpointMeanCutoff 36 22) (endpointMeanBox 36 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 36 22 h) (endpointMeanCornerA 36 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 22, endpointJoint24Q (endpointMeanCornerK 36 22 h) (endpointMeanCornerA 36 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 36 22, endpointRunWeightQ (endpointMeanCutoff 36 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 36 22) = (97400241/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 36 22 h = (logRoundedQ ((endpointMeanCutoff 36 22:ℚ)/200)).2+(97400241/250000000000000:ℚ)+((endpointMeanRuns 36 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 36 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 36 22) r*endpointJoint24Q (endpointMeanCornerK 36 22 h) (endpointMeanCornerA 36 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 36 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 36 22 h≤endpointMeanCorner 36 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 36 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint36_22

namespace EndpointAnalyticJoint36_23
private noncomputable def weights : IntegerLookupTree := (.branch 1277 (.leaf (68706580900000:ℤ)) (.branch 2605 (.leaf (49148632300000:ℤ)) (.leaf (3807508100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2070639052631978:ℤ)) (.branch 151 (.leaf (2475015372064837:ℤ)) (.leaf (3538157210228413:ℤ)))), (.branch 125 (.leaf (2087620683585788:ℤ)) (.branch 151 (.leaf (2505465937618499:ℤ)) (.leaf (3617269050370541:ℤ)))), (.branch 125 (.leaf (2087254270816324:ℤ)) (.branch 151 (.leaf (2511226233620565:ℤ)) (.leaf (3676905760777625:ℤ)))), (.branch 125 (.leaf (2105103532445159:ℤ)) (.branch 151 (.leaf (2543728172563892:ℤ)) (.leaf (3765412033683174:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 36 23) 8000 (endpointMeanRuns 36 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 36 23, EndpointRunConditions (endpointMeanCutoff 36 23) (endpointMeanBox 36 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 36 23 h) (endpointMeanCornerA 36 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 23, endpointJoint24Q (endpointMeanCornerK 36 23 h) (endpointMeanCornerA 36 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 36 23, endpointRunWeightQ (endpointMeanCutoff 36 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 36 23) = (194210891/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 36 23 h = (logRoundedQ ((endpointMeanCutoff 36 23:ℚ)/200)).2+(194210891/500000000000000:ℚ)+((endpointMeanRuns 36 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 36 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 36 23) r*endpointJoint24Q (endpointMeanCornerK 36 23 h) (endpointMeanCornerA 36 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 36 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 36 23 h≤endpointMeanCorner 36 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 36 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint36_23

namespace EndpointAnalyticJoint36_24
private noncomputable def weights : IntegerLookupTree := (.branch 1277 (.leaf (66096665200000:ℤ)) (.branch 2605 (.leaf (48852499500000:ℤ)) (.leaf (3790905200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2087620683585788:ℤ)) (.branch 151 (.leaf (2505465937618499:ℤ)) (.leaf (3617269050370541:ℤ)))), (.branch 125 (.leaf (2104741583520097:ℤ)) (.branch 151 (.leaf (2536291142034212:ℤ)) (.leaf (3698149800959205:ℤ)))), (.branch 125 (.leaf (2105103532445159:ℤ)) (.branch 151 (.leaf (2543728172563892:ℤ)) (.leaf (3765412033683174:ℤ)))), (.branch 125 (.leaf (2123105432947543:ℤ)) (.branch 151 (.leaf (2576650772943833:ℤ)) (.leaf (3856048728430699:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 36 24) 8000 (endpointMeanRuns 36 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 36 24, EndpointRunConditions (endpointMeanCutoff 36 24) (endpointMeanBox 36 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 36 24 h) (endpointMeanCornerA 36 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 24, endpointJoint24Q (endpointMeanCornerK 36 24 h) (endpointMeanCornerA 36 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 36 24, endpointRunWeightQ (endpointMeanCutoff 36 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 36 24) = (387254557/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 36 24 h = (logRoundedQ ((endpointMeanCutoff 36 24:ℚ)/200)).2+(387254557/1000000000000000:ℚ)+((endpointMeanRuns 36 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 36 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 36 24) r*endpointJoint24Q (endpointMeanCornerK 36 24 h) (endpointMeanCornerA 36 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 36 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 36 24 h≤endpointMeanCorner 36 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 36 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint36_24

namespace EndpointAnalyticJoint36_25
private noncomputable def weights : IntegerLookupTree := (.branch 1277 (.leaf (63263710800000:ℤ)) (.branch 2605 (.leaf (48522900300000:ℤ)) (.leaf (3772425900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2104741583520097:ℤ)) (.branch 151 (.leaf (2536291142034212:ℤ)) (.leaf (3698149800959205:ℤ)))), (.branch 125 (.leaf (2122002894601351:ℤ)) (.branch 151 (.leaf (2567495594562217:ℤ)) (.leaf (3780839014154522:ℤ)))), (.branch 125 (.leaf (2123105432947543:ℤ)) (.branch 151 (.leaf (2576650772943833:ℤ)) (.leaf (3856048728430699:ℤ)))), (.branch 125 (.leaf (2141261277622598:ℤ)) (.branch 151 (.leaf (2609999479236919:ℤ)) (.leaf (3948867126099777:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 36 25) 8000 (endpointMeanRuns 36 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 36 25, EndpointRunConditions (endpointMeanCutoff 36 25) (endpointMeanBox 36 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 36 25 h) (endpointMeanCornerA 36 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 25, endpointJoint24Q (endpointMeanCornerK 36 25 h) (endpointMeanCornerA 36 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 36 25, endpointRunWeightQ (endpointMeanCutoff 36 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 36 25) = (385955421/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 36 25 h = (logRoundedQ ((endpointMeanCutoff 36 25:ℚ)/200)).2+(385955421/1000000000000000:ℚ)+((endpointMeanRuns 36 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 36 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 36 25) r*endpointJoint24Q (endpointMeanCornerK 36 25 h) (endpointMeanCornerA 36 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 36 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 36 25 h≤endpointMeanCorner 36 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 36 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint36_25

namespace EndpointAnalyticJoint36_26
private noncomputable def weights : IntegerLookupTree := (.branch 1481 (.leaf (83495770400000:ℤ)) (.leaf (61613726900000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 144 (.leaf (2122002894601351:ℤ)) (.leaf (3353730697273941:ℤ))), (.branch 144 (.leaf (2139405768363065:ℤ)) (.leaf (3417544609673249:ℤ))), (.branch 144 (.leaf (2141261277622598:ℤ)) (.leaf (3466135702815248:ℤ))), (.branch 144 (.leaf (2159572382931793:ℤ)) (.leaf (3536569817841813:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 36 26) 8000 (endpointMeanRuns 36 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 36 26, EndpointRunConditions (endpointMeanCutoff 36 26) (endpointMeanBox 36 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 36 26 h) (endpointMeanCornerA 36 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 26, endpointJoint24Q (endpointMeanCornerK 36 26 h) (endpointMeanCornerA 36 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 36 26, endpointRunWeightQ (endpointMeanCutoff 36 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 36 26) = (76962563/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 36 26 h = (logRoundedQ ((endpointMeanCutoff 36 26:ℚ)/200)).2+(76962563/200000000000000:ℚ)+((endpointMeanRuns 36 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 36 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 36 26) r*endpointJoint24Q (endpointMeanCornerK 36 26 h) (endpointMeanCornerA 36 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 36 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 36 26 h≤endpointMeanCorner 36 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 36 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint36_26

namespace EndpointAnalyticJoint36_27
private noncomputable def weights : IntegerLookupTree := (.branch 1481 (.leaf (80697757500000:ℤ)) (.leaf (61279043200000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 144 (.leaf (2139405768363065:ℤ)) (.leaf (3417544609673249:ℤ))), (.branch 144 (.leaf (2156951365782668:ℤ)) (.leaf (3482572756542553:ℤ))), (.branch 144 (.leaf (2159572382931793:ℤ)) (.leaf (3536569817841813:ℤ))), (.branch 144 (.leaf (2178040076594380:ℤ)) (.leaf (3608435199554081:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 36 27) 8000 (endpointMeanRuns 36 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 36 27, EndpointRunConditions (endpointMeanCutoff 36 27) (endpointMeanBox 36 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 36 27 h) (endpointMeanCornerA 36 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 27, endpointJoint24Q (endpointMeanCornerK 36 27 h) (endpointMeanCornerA 36 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 36 27, endpointRunWeightQ (endpointMeanCutoff 36 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 36 27) = (383681439/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 36 27 h = (logRoundedQ ((endpointMeanCutoff 36 27:ℚ)/200)).2+(383681439/1000000000000000:ℚ)+((endpointMeanRuns 36 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 36 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 36 27) r*endpointJoint24Q (endpointMeanCornerK 36 27 h) (endpointMeanCornerA 36 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 36 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 36 27 h≤endpointMeanCorner 36 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 36 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint36_27

namespace EndpointAnalyticJoint36_28
private noncomputable def weights : IntegerLookupTree := (.branch 1761 (.leaf (102860794600000:ℤ)) (.leaf (30913844000000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 137 (.leaf (2156951365782668:ℤ)) (.leaf (3112157204815632:ℤ))), (.branch 137 (.leaf (2174640857358941:ℤ)) (.leaf (3162613805464861:ℤ))), (.branch 137 (.leaf (2178040076594380:ℤ)) (.leaf (3198197028975140:ℤ))), (.branch 137 (.leaf (2196665697683672:ℤ)) (.leaf (3253215556140194:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 36 28) 8000 (endpointMeanRuns 36 28) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 36 28, EndpointRunConditions (endpointMeanCutoff 36 28) (endpointMeanBox 36 28).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 28, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 36 28 h) (endpointMeanCornerA 36 28 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 36 28, endpointJoint24Q (endpointMeanCornerK 36 28 h) (endpointMeanCornerA 36 28 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 36 28, endpointRunWeightQ (endpointMeanCutoff 36 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 36 28) = (11950681/31250000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 36 28 h = (logRoundedQ ((endpointMeanCutoff 36 28:ℚ)/200)).2+(11950681/31250000000000:ℚ)+((endpointMeanRuns 36 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 36 28).map (fun r => endpointRunWeightQ (endpointMeanCutoff 36 28) r*endpointJoint24Q (endpointMeanCornerK 36 28 h) (endpointMeanCornerA 36 28 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 36 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 36 28 h≤endpointMeanCorner 36 28 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 36 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint36_28

namespace EndpointAnalyticJoint37_14
private noncomputable def weights : IntegerLookupTree := (.branch 1085 (.leaf (60822221900000:ℤ)) (.branch 1730 (.leaf (49696671900000:ℤ)) (.leaf (35520602400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 137 (.leaf (1940992718599444:ℤ)) (.branch 159 (.leaf (2539023619147209:ℤ)) (.leaf (3368256826076988:ℤ)))), (.branch 137 (.leaf (1949802150683548:ℤ)) (.branch 159 (.leaf (2562159090621630:ℤ)) (.leaf (3420582123186340:ℤ)))), (.branch 137 (.leaf (1951435638957084:ℤ)) (.branch 159 (.leaf (2579400086080124:ℤ)) (.leaf (3510017062143601:ℤ)))), (.branch 137 (.leaf (1960679125737979:ℤ)) (.branch 159 (.leaf (2604413359458478:ℤ)) (.leaf (3569950017031878:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 37 14) 8000 (endpointMeanRuns 37 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 37 14, EndpointRunConditions (endpointMeanCutoff 37 14) (endpointMeanBox 37 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 37 14 h) (endpointMeanCornerA 37 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 14, endpointJoint24Q (endpointMeanCornerK 37 14 h) (endpointMeanCornerA 37 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 37 14, endpointRunWeightQ (endpointMeanCutoff 37 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 37 14) = (198391879/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 37 14 h = (logRoundedQ ((endpointMeanCutoff 37 14:ℚ)/200)).2+(198391879/500000000000000:ℚ)+((endpointMeanRuns 37 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 37 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 37 14) r*endpointJoint24Q (endpointMeanCornerK 37 14 h) (endpointMeanCornerA 37 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 37 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 37 14 h≤endpointMeanCorner 37 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 37 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint37_14

namespace EndpointAnalyticJoint37_15
private noncomputable def weights : IntegerLookupTree := (.branch 1104 (.leaf (61845950800000:ℤ)) (.branch 1730 (.leaf (46302908000000:ℤ)) (.leaf (35378291300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 137 (.leaf (1949802150683548:ℤ)) (.branch 158 (.leaf (2562159090621630:ℤ)) (.leaf (3366829481149245:ℤ)))), (.branch 137 (.leaf (1966475983478444:ℤ)) (.branch 158 (.leaf (2606235868334639:ℤ)) (.leaf (3463349765575030:ℤ)))), (.branch 137 (.leaf (1960679125737979:ℤ)) (.branch 158 (.leaf (2604413359458478:ℤ)) (.leaf (3506574103774844:ℤ)))), (.branch 137 (.leaf (1978179478307678:ℤ)) (.branch 158 (.leaf (2652107522424872:ℤ)) (.leaf (3616893434609924:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 37 15) 8000 (endpointMeanRuns 37 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 37 15, EndpointRunConditions (endpointMeanCutoff 37 15) (endpointMeanBox 37 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 37 15 h) (endpointMeanCornerA 37 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 15, endpointJoint24Q (endpointMeanCornerK 37 15 h) (endpointMeanCornerA 37 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 37 15, endpointRunWeightQ (endpointMeanCutoff 37 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 37 15) = (197920731/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 37 15 h = (logRoundedQ ((endpointMeanCutoff 37 15:ℚ)/200)).2+(197920731/500000000000000:ℚ)+((endpointMeanRuns 37 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 37 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 37 15) r*endpointJoint24Q (endpointMeanCornerK 37 15 h) (endpointMeanCornerA 37 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 37 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 37 15 h≤endpointMeanCorner 37 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 37 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint37_15

namespace EndpointAnalyticJoint37_16
private noncomputable def weights : IntegerLookupTree := (.branch 1561 (.leaf (121604785700000:ℤ)) (.branch 2561 (.leaf (22113221400000:ℤ)) (.leaf (4356400400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (1966475983478444:ℤ)) (.branch 141 (.leaf (2295048232369015:ℤ)) (.leaf (2731465677931144:ℤ)))), (.branch 125 (.leaf (1983292403407101:ℤ)) (.branch 141 (.leaf (2324752253664182:ℤ)) (.leaf (2783135695199034:ℤ)))), (.branch 125 (.leaf (1978179478307678:ℤ)) (.branch 141 (.leaf (2320535328304589:ℤ)) (.leaf (2787940838019306:ℤ)))), (.branch 125 (.leaf (1995836033050416:ℤ)) (.branch 141 (.leaf (2352192267357482:ℤ)) (.leaf (2844314890998360:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 37 16) 8000 (endpointMeanRuns 37 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 37 16, EndpointRunConditions (endpointMeanCutoff 37 16) (endpointMeanBox 37 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 37 16 h) (endpointMeanCornerA 37 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 16, endpointJoint24Q (endpointMeanCornerK 37 16 h) (endpointMeanCornerA 37 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 37 16, endpointRunWeightQ (endpointMeanCutoff 37 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 37 16) = (394442323/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 37 16 h = (logRoundedQ ((endpointMeanCutoff 37 16:ℚ)/200)).2+(394442323/1000000000000000:ℚ)+((endpointMeanRuns 37 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 37 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 37 16) r*endpointJoint24Q (endpointMeanCornerK 37 16 h) (endpointMeanCornerA 37 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 37 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 37 16 h≤endpointMeanCorner 37 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 37 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint37_16

namespace EndpointAnalyticJoint37_17
private noncomputable def weights : IntegerLookupTree := (.branch 1231 (.leaf (75222438100000:ℤ)) (.branch 2561 (.leaf (57131671200000:ℤ)) (.leaf (4336704600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (1983292403407101:ℤ)) (.branch 152 (.leaf (2324752253664182:ℤ)) (.leaf (3235850913769786:ℤ)))), (.branch 125 (.leaf (2000252629810687:ℤ)) (.branch 152 (.leaf (2354840723908469:ℤ)) (.leaf (3315677710635196:ℤ)))), (.branch 125 (.leaf (1995836033050416:ℤ)) (.branch 152 (.leaf (2352192267357482:ℤ)) (.leaf (3350237430830962:ℤ)))), (.branch 125 (.leaf (2013650184173460:ℤ)) (.branch 152 (.leaf (2384281073048203:ℤ)) (.leaf (3439908317948524:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 37 17) 8000 (endpointMeanRuns 37 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 37 17, EndpointRunConditions (endpointMeanCutoff 37 17) (endpointMeanBox 37 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 37 17 h) (endpointMeanCornerA 37 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 17, endpointJoint24Q (endpointMeanCornerK 37 17 h) (endpointMeanCornerA 37 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 37 17, endpointRunWeightQ (endpointMeanCutoff 37 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 37 17) = (393212761/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 37 17 h = (logRoundedQ ((endpointMeanCutoff 37 17:ℚ)/200)).2+(393212761/1000000000000000:ℚ)+((endpointMeanRuns 37 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 37 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 37 17) r*endpointJoint24Q (endpointMeanCornerK 37 17 h) (endpointMeanCornerA 37 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 37 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 37 17 h≤endpointMeanCorner 37 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 37 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint37_17

namespace EndpointAnalyticJoint37_18
private noncomputable def weights : IntegerLookupTree := (.branch 1489 (.leaf (105231855300000:ℤ)) (.branch 2561 (.leaf (27065728200000:ℤ)) (.leaf (4314795300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2000252629810687:ℤ)) (.branch 143 (.leaf (2354840723908469:ℤ)) (.leaf (2911393083807970:ℤ)))), (.branch 125 (.leaf (2017357892457629:ℤ)) (.branch 143 (.leaf (2385318618892623:ℤ)) (.leaf (2969156466817806:ℤ)))), (.branch 125 (.leaf (2013650184173460:ℤ)) (.branch 143 (.leaf (2384281073048203:ℤ)) (.leaf (2985035763664251:ℤ)))), (.branch 125 (.leaf (2031623338328309:ℤ)) (.branch 143 (.leaf (2416807636937927:ℤ)) (.leaf (3048487947527376:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 37 18) 8000 (endpointMeanRuns 37 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 37 18, EndpointRunConditions (endpointMeanCutoff 37 18) (endpointMeanBox 37 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 37 18 h) (endpointMeanCornerA 37 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 18, endpointJoint24Q (endpointMeanCornerK 37 18 h) (endpointMeanCornerA 37 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 37 18, endpointRunWeightQ (endpointMeanCutoff 37 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 37 18) = (391845023/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 37 18 h = (logRoundedQ ((endpointMeanCutoff 37 18:ℚ)/200)).2+(391845023/1000000000000000:ℚ)+((endpointMeanRuns 37 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 37 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 37 18) r*endpointJoint24Q (endpointMeanCornerK 37 18 h) (endpointMeanCornerA 37 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 37 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 37 18 h≤endpointMeanCorner 37 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 37 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint37_18

namespace EndpointAnalyticJoint37_19
private noncomputable def weights : IntegerLookupTree := (.branch 1489 (.leaf (101770835500000:ℤ)) (.branch 2561 (.leaf (26911556400000:ℤ)) (.leaf (4295536600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2017357892457629:ℤ)) (.branch 143 (.leaf (2385318618892623:ℤ)) (.leaf (2969156466817806:ℤ)))), (.branch 125 (.leaf (2034609431632777:ℤ)) (.branch 143 (.leaf (2416190978807351:ℤ)) (.leaf (3028065902016644:ℤ)))), (.branch 125 (.leaf (2031623338328309:ℤ)) (.branch 143 (.leaf (2416807636937927:ℤ)) (.leaf (3048487947527376:ℤ)))), (.branch 125 (.leaf (2049756914721743:ℤ)) (.branch 143 (.leaf (2449777930960994:ℤ)) (.leaf (3113288919128998:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 37 19) 8000 (endpointMeanRuns 37 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 37 19, EndpointRunConditions (endpointMeanCutoff 37 19) (endpointMeanBox 37 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 37 19 h) (endpointMeanCornerA 37 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 19, endpointJoint24Q (endpointMeanCornerK 37 19 h) (endpointMeanCornerA 37 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 37 19, endpointRunWeightQ (endpointMeanCutoff 37 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 37 19) = (1562571/4000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 37 19 h = (logRoundedQ ((endpointMeanCutoff 37 19:ℚ)/200)).2+(1562571/4000000000000:ℚ)+((endpointMeanRuns 37 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 37 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 37 19) r*endpointJoint24Q (endpointMeanCornerK 37 19 h) (endpointMeanCornerA 37 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 37 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 37 19 h≤endpointMeanCorner 37 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 37 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint37_19

namespace EndpointAnalyticJoint37_20
private noncomputable def weights : IntegerLookupTree := (.branch 1489 (.leaf (98418209300000:ℤ)) (.branch 2561 (.leaf (26758978000000:ℤ)) (.leaf (4276476900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2034609431632777:ℤ)) (.branch 143 (.leaf (2416190978807351:ℤ)) (.leaf (3028065902016644:ℤ)))), (.branch 125 (.leaf (2052008498227335:ℤ)) (.branch 143 (.leaf (2447462909076812:ℤ)) (.leaf (3088144127609053:ℤ)))), (.branch 125 (.leaf (2049756914721743:ℤ)) (.branch 143 (.leaf (2449777930960994:ℤ)) (.leaf (3113288919128998:ℤ)))), (.branch 125 (.leaf (2068052345227901:ℤ)) (.branch 143 (.leaf (2483198008521375:ℤ)) (.leaf (3179467349324121:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 37 20) 8000 (endpointMeanRuns 37 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 37 20, EndpointRunConditions (endpointMeanCutoff 37 20) (endpointMeanBox 37 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 37 20 h) (endpointMeanCornerA 37 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 20, endpointJoint24Q (endpointMeanCornerK 37 20 h) (endpointMeanCornerA 37 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 37 20, endpointRunWeightQ (endpointMeanCutoff 37 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 37 20) = (48681613/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 37 20 h = (logRoundedQ ((endpointMeanCutoff 37 20:ℚ)/200)).2+(48681613/125000000000000:ℚ)+((endpointMeanRuns 37 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 37 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 37 20) r*endpointJoint24Q (endpointMeanCornerK 37 20 h) (endpointMeanCornerA 37 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 37 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 37 20 h≤endpointMeanCorner 37 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 37 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint37_20

namespace EndpointAnalyticJoint37_21
private noncomputable def weights : IntegerLookupTree := (.branch 1489 (.leaf (94771688900000:ℤ)) (.branch 2561 (.leaf (26589191600000:ℤ)) (.leaf (4255267600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2052008498227335:ℤ)) (.branch 143 (.leaf (2447462909076812:ℤ)) (.leaf (3088144127609053:ℤ)))), (.branch 125 (.leaf (2069556353829584:ℤ)) (.branch 143 (.leaf (2479139581202922:ℤ)) (.leaf (3149414332936101:ℤ)))), (.branch 125 (.leaf (2068052345227901:ℤ)) (.branch 143 (.leaf (2483198008521375:ℤ)) (.leaf (3179467349324121:ℤ)))), (.branch 125 (.leaf (2086511074501343:ℤ)) (.branch 143 (.leaf (2517074005604113:ℤ)) (.leaf (3247052518417192:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 37 21) 8000 (endpointMeanRuns 37 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 37 21, EndpointRunConditions (endpointMeanCutoff 37 21) (endpointMeanBox 37 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 37 21 h) (endpointMeanCornerA 37 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 21, endpointJoint24Q (endpointMeanCornerK 37 21 h) (endpointMeanCornerA 37 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 37 21, endpointRunWeightQ (endpointMeanCutoff 37 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 37 21) = (12129027/31250000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 37 21 h = (logRoundedQ ((endpointMeanCutoff 37 21:ℚ)/200)).2+(12129027/31250000000000:ℚ)+((endpointMeanRuns 37 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 37 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 37 21) r*endpointJoint24Q (endpointMeanCornerK 37 21 h) (endpointMeanCornerA 37 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 37 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 37 21 h≤endpointMeanCorner 37 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 37 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint37_21

namespace EndpointAnalyticJoint37_22
private noncomputable def weights : IntegerLookupTree := (.branch 1642 (.leaf (107278118400000:ℤ)) (.branch 2561 (.leaf (16714247900000:ℤ)) (.leaf (4236617600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2069556353829584:ℤ)) (.branch 139 (.leaf (2479139581202922:ℤ)) (.leaf (2969251423354972:ℤ)))), (.branch 125 (.leaf (2087254270816324:ℤ)) (.branch 139 (.leaf (2511226233620565:ℤ)) (.leaf (3022812219589175:ℤ)))), (.branch 125 (.leaf (2086511074501343:ℤ)) (.branch 139 (.leaf (2517074005604113:ℤ)) (.leaf (3047365300022244:ℤ)))), (.branch 125 (.leaf (2105134560091123:ℤ)) (.branch 139 (.leaf (2551412141901845:ℤ)) (.leaf (3105999128135948:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 37 22) 8000 (endpointMeanRuns 37 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 37 22, EndpointRunConditions (endpointMeanCutoff 37 22) (endpointMeanBox 37 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 37 22 h) (endpointMeanCornerA 37 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 22, endpointJoint24Q (endpointMeanCornerK 37 22 h) (endpointMeanCornerA 37 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 37 22, endpointRunWeightQ (endpointMeanCutoff 37 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 37 22) = (38696459/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 37 22 h = (logRoundedQ ((endpointMeanCutoff 37 22:ℚ)/200)).2+(38696459/100000000000000:ℚ)+((endpointMeanRuns 37 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 37 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 37 22) r*endpointJoint24Q (endpointMeanCornerK 37 22 h) (endpointMeanCornerA 37 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 37 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 37 22 h≤endpointMeanCorner 37 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 37 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint37_22

namespace EndpointAnalyticJoint37_23
private noncomputable def weights : IntegerLookupTree := (.branch 1561 (.leaf (95695942200000:ℤ)) (.branch 2561 (.leaf (21223074600000:ℤ)) (.leaf (4215859300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2087254270816324:ℤ)) (.branch 141 (.leaf (2511226233620565:ℤ)) (.leaf (3114341142930930:ℤ)))), (.branch 125 (.leaf (2105103532445159:ℤ)) (.branch 141 (.leaf (2543728172563892:ℤ)) (.leaf (3173253858522959:ℤ)))), (.branch 125 (.leaf (2105134560091123:ℤ)) (.branch 141 (.leaf (2551412141901845:ℤ)) (.leaf (3207320823277326:ℤ)))), (.branch 125 (.leaf (2123924272555875:ℤ)) (.branch 141 (.leaf (2586218721956809:ℤ)) (.leaf (3272175023749065:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 37 23) 8000 (endpointMeanRuns 37 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 37 23, EndpointRunConditions (endpointMeanCutoff 37 23) (endpointMeanBox 37 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 37 23 h) (endpointMeanCornerA 37 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 23, endpointJoint24Q (endpointMeanCornerK 37 23 h) (endpointMeanCornerA 37 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 37 23, endpointRunWeightQ (endpointMeanCutoff 37 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 37 23) = (77133741/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 37 23 h = (logRoundedQ ((endpointMeanCutoff 37 23:ℚ)/200)).2+(77133741/200000000000000:ℚ)+((endpointMeanRuns 37 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 37 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 37 23) r*endpointJoint24Q (endpointMeanCornerK 37 23 h) (endpointMeanCornerA 37 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 37 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 37 23 h≤endpointMeanCorner 37 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 37 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint37_23

namespace EndpointAnalyticJoint37_24
private noncomputable def weights : IntegerLookupTree := (.branch 1334 (.leaf (68268944800000:ℤ)) (.branch 2561 (.leaf (40878687100000:ℤ)) (.leaf (4197601700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2105103532445159:ℤ)) (.branch 148 (.leaf (2543728172563892:ℤ)) (.leaf (3564664575760377:ℤ)))), (.branch 125 (.leaf (2123105432947543:ℤ)) (.branch 148 (.leaf (2576650772943833:ℤ)) (.leaf (3644422352960535:ℤ)))), (.branch 125 (.leaf (2123924272555875:ℤ)) (.branch 148 (.leaf (2586218721956809:ℤ)) (.leaf (3714254706391952:ℤ)))), (.branch 125 (.leaf (2142881695579942:ℤ)) (.branch 148 (.leaf (2621500136318320:ℤ)) (.leaf (3803869325954282:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 37 24) 8000 (endpointMeanRuns 37 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 37 24, EndpointRunConditions (endpointMeanCutoff 37 24) (endpointMeanBox 37 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 37 24 h) (endpointMeanCornerA 37 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 24, endpointJoint24Q (endpointMeanCornerK 37 24 h) (endpointMeanCornerA 37 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 37 24, endpointRunWeightQ (endpointMeanCutoff 37 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 37 24) = (384528927/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 37 24 h = (logRoundedQ ((endpointMeanCutoff 37 24:ℚ)/200)).2+(384528927/1000000000000000:ℚ)+((endpointMeanRuns 37 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 37 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 37 24) r*endpointJoint24Q (endpointMeanCornerK 37 24 h) (endpointMeanCornerA 37 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 37 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 37 24 h≤endpointMeanCorner 37 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 37 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint37_24

namespace EndpointAnalyticJoint37_25
private noncomputable def weights : IntegerLookupTree := (.branch 2207 (.leaf (138969360800000:ℤ)) (.leaf (10237250500000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 129 (.leaf (2123105432947543:ℤ)) (.leaf (2713775526697958:ℤ))), (.branch 129 (.leaf (2141261277622598:ℤ)) (.leaf (2752403369471495:ℤ))), (.branch 129 (.leaf (2142881695579942:ℤ)) (.leaf (2768714787282273:ℤ))), (.branch 129 (.leaf (2162008326090530:ℤ)) (.leaf (2810376798338642:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 37 25) 8000 (endpointMeanRuns 37 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 37 25, EndpointRunConditions (endpointMeanCutoff 37 25) (endpointMeanBox 37 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 37 25 h) (endpointMeanCornerA 37 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 25, endpointJoint24Q (endpointMeanCornerK 37 25 h) (endpointMeanCornerA 37 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 37 25, endpointRunWeightQ (endpointMeanCutoff 37 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 37 25) = (383260023/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 37 25 h = (logRoundedQ ((endpointMeanCutoff 37 25:ℚ)/200)).2+(383260023/1000000000000000:ℚ)+((endpointMeanRuns 37 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 37 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 37 25) r*endpointJoint24Q (endpointMeanCornerK 37 25 h) (endpointMeanCornerA 37 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 37 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 37 25 h≤endpointMeanCorner 37 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 37 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint37_25

namespace EndpointAnalyticJoint37_26
private noncomputable def weights : IntegerLookupTree := (.branch 2207 (.leaf (135133184200000:ℤ)) (.leaf (10190745400000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 129 (.leaf (2141261277622598:ℤ)) (.leaf (2752403369471495:ℤ))), (.branch 129 (.leaf (2159572382931793:ℤ)) (.leaf (2791581040417128:ℤ))), (.branch 129 (.leaf (2162008326090530:ℤ)) (.leaf (2810376798338642:ℤ))), (.branch 129 (.leaf (2181305674375896:ℤ)) (.leaf (2852665715125144:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 37 26) 8000 (endpointMeanRuns 37 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 37 26, EndpointRunConditions (endpointMeanCutoff 37 26) (endpointMeanBox 37 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 37 26 h) (endpointMeanCornerA 37 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 26, endpointJoint24Q (endpointMeanCornerK 37 26 h) (endpointMeanCornerA 37 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 37 26, endpointRunWeightQ (endpointMeanCutoff 37 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 37 26) = (95535933/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 37 26 h = (logRoundedQ ((endpointMeanCutoff 37 26:ℚ)/200)).2+(95535933/250000000000000:ℚ)+((endpointMeanRuns 37 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 37 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 37 26) r*endpointJoint24Q (endpointMeanCornerK 37 26 h) (endpointMeanCornerA 37 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 37 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 37 26 h≤endpointMeanCorner 37 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 37 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint37_26

namespace EndpointAnalyticJoint37_27
private noncomputable def weights : IntegerLookupTree := (.branch 2207 (.leaf (131404797100000:ℤ)) (.leaf (10144686900000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 129 (.leaf (2159572382931793:ℤ)) (.leaf (2791581040417128:ℤ))), (.branch 129 (.leaf (2178040076594380:ℤ)) (.leaf (2831316365781351:ℤ))), (.branch 129 (.leaf (2181305674375896:ℤ)) (.leaf (2852665715125144:ℤ))), (.branch 129 (.leaf (2200775264204627:ℤ)) (.leaf (2895590970954884:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 37 27) 8000 (endpointMeanRuns 37 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 37 27, EndpointRunConditions (endpointMeanCutoff 37 27) (endpointMeanBox 37 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 37 27 h) (endpointMeanCornerA 37 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 27, endpointJoint24Q (endpointMeanCornerK 37 27 h) (endpointMeanCornerA 37 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 37 27, endpointRunWeightQ (endpointMeanCutoff 37 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 37 27) = (190519081/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 37 27 h = (logRoundedQ ((endpointMeanCutoff 37 27:ℚ)/200)).2+(190519081/500000000000000:ℚ)+((endpointMeanRuns 37 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 37 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 37 27) r*endpointJoint24Q (endpointMeanCornerK 37 27 h) (endpointMeanCornerA 37 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 37 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 37 27 h≤endpointMeanCorner 37 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 37 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint37_27

namespace EndpointAnalyticJoint37_28
private noncomputable def weights : IntegerLookupTree := (.branch 2207 (.leaf (127335244800000:ℤ)) (.leaf (10093394400000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 129 (.leaf (2178040076594380:ℤ)) (.leaf (2831316365781351:ℤ))), (.branch 129 (.leaf (2196665697683672:ℤ)) (.leaf (2871617283209336:ℤ))), (.branch 129 (.leaf (2200775264204627:ℤ)) (.leaf (2895590970954884:ℤ))), (.branch 129 (.leaf (2220418632945936:ℤ)) (.leaf (2939162141087965:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 37 28) 8000 (endpointMeanRuns 37 28) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 37 28, EndpointRunConditions (endpointMeanCutoff 37 28) (endpointMeanBox 37 28).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 28, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 37 28 h) (endpointMeanCornerA 37 28 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 28, endpointJoint24Q (endpointMeanCornerK 37 28 h) (endpointMeanCornerA 37 28 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 37 28, endpointRunWeightQ (endpointMeanCutoff 37 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 37 28) = (94951739/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 37 28 h = (logRoundedQ ((endpointMeanCutoff 37 28:ℚ)/200)).2+(94951739/250000000000000:ℚ)+((endpointMeanRuns 37 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 37 28).map (fun r => endpointRunWeightQ (endpointMeanCutoff 37 28) r*endpointJoint24Q (endpointMeanCornerK 37 28 h) (endpointMeanCornerA 37 28 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 37 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 37 28 h≤endpointMeanCorner 37 28 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 37 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint37_28

namespace EndpointAnalyticJoint37_29
private noncomputable def weights : IntegerLookupTree := (.branch 1601 (.leaf (81736509400000:ℤ)) (.leaf (44881991200000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 140 (.leaf (2196665697683672:ℤ)) (.leaf (3423971443277048:ℤ))), (.branch 140 (.leaf (2207917436840946:ℤ)) (.leaf (3461781047279692:ℤ))), (.branch 140 (.leaf (2220418632945936:ℤ)) (.leaf (3548157128986134:ℤ))), (.branch 140 (.leaf (2232288712748226:ℤ)) (.leaf (3589983323937621:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 37 29) 8000 (endpointMeanRuns 37 29) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 37 29, EndpointRunConditions (endpointMeanCutoff 37 29) (endpointMeanBox 37 29).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 29, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 37 29 h) (endpointMeanCornerA 37 29 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 37 29, endpointJoint24Q (endpointMeanCornerK 37 29 h) (endpointMeanCornerA 37 29 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 37 29, endpointRunWeightQ (endpointMeanCutoff 37 29) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 37 29) = (189429187/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 37 29 h = (logRoundedQ ((endpointMeanCutoff 37 29:ℚ)/200)).2+(189429187/500000000000000:ℚ)+((endpointMeanRuns 37 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 37 29).map (fun r => endpointRunWeightQ (endpointMeanCutoff 37 29) r*endpointJoint24Q (endpointMeanCornerK 37 29 h) (endpointMeanCornerA 37 29 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 37 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 37 29 h≤endpointMeanCorner 37 29 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 37 29 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint37_29

namespace EndpointAnalyticJoint38_15
private noncomputable def weights : IntegerLookupTree := (.branch 1166 (.leaf (65991885800000:ℤ)) (.branch 2622 (.leaf (71080452000000:ℤ)) (.leaf (3994205400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (1948455608364376:ℤ)) (.branch 154 (.leaf (2274057607689020:ℤ)) (.leaf (3300988195070925:ℤ)))), (.branch 124 (.leaf (1961271857440384:ℤ)) (.branch 154 (.leaf (2296931676519408:ℤ)) (.leaf (3371258077170859:ℤ)))), (.branch 124 (.leaf (1959850160446037:ℤ)) (.branch 154 (.leaf (2299509535038063:ℤ)) (.leaf (3440397575801926:ℤ)))), (.branch 124 (.leaf (1973312604772299:ℤ)) (.branch 154 (.leaf (2323923578981319:ℤ)) (.leaf (3520859303623255:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 38 15) 8000 (endpointMeanRuns 38 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 38 15, EndpointRunConditions (endpointMeanCutoff 38 15) (endpointMeanBox 38 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 38 15 h) (endpointMeanCornerA 38 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 15, endpointJoint24Q (endpointMeanCornerK 38 15 h) (endpointMeanCornerA 38 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 38 15, endpointRunWeightQ (endpointMeanCutoff 38 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 38 15) = (392755041/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 38 15 h = (logRoundedQ ((endpointMeanCutoff 38 15:ℚ)/200)).2+(392755041/1000000000000000:ℚ)+((endpointMeanRuns 38 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 38 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 38 15) r*endpointJoint24Q (endpointMeanCornerK 38 15 h) (endpointMeanCornerA 38 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 38 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 38 15 h≤endpointMeanCorner 38 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 38 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint38_15

namespace EndpointAnalyticJoint38_16
private noncomputable def weights : IntegerLookupTree := (.branch 1311 (.leaf (84215207300000:ℤ)) (.branch 1967 (.leaf (30030830600000:ℤ)) (.leaf (20505457400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 132 (.leaf (1961271857440384:ℤ)) (.branch 148 (.leaf (2501889417264974:ℤ)) (.leaf (3069307687165468:ℤ)))), (.branch 132 (.leaf (1978334329148231:ℤ)) (.branch 148 (.leaf (2542407842973108:ℤ)) (.leaf (3143361531731304:ℤ)))), (.branch 132 (.leaf (1973312604772299:ℤ)) (.branch 148 (.leaf (2542369017111681:ℤ)) (.leaf (3169803679069188:ℤ)))), (.branch 132 (.leaf (1991241392007725:ℤ)) (.branch 148 (.leaf (2586135951001491:ℤ)) (.leaf (3252825517108794:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 38 16) 8000 (endpointMeanRuns 38 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 38 16, EndpointRunConditions (endpointMeanCutoff 38 16) (endpointMeanBox 38 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 38 16 h) (endpointMeanCornerA 38 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 16, endpointJoint24Q (endpointMeanCornerK 38 16 h) (endpointMeanCornerA 38 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 38 16, endpointRunWeightQ (endpointMeanCutoff 38 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 38 16) = (7833881/20000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 38 16 h = (logRoundedQ ((endpointMeanCutoff 38 16:ℚ)/200)).2+(7833881/20000000000000:ℚ)+((endpointMeanRuns 38 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 38 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 38 16) r*endpointJoint24Q (endpointMeanCornerK 38 16 h) (endpointMeanCornerA 38 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 38 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 38 16 h≤endpointMeanCorner 38 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 38 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint38_16

namespace EndpointAnalyticJoint38_17
private noncomputable def weights : IntegerLookupTree := (.branch 1701 (.leaf (125503607300000:ℤ)) (.branch 2622 (.leaf (15081867400000:ℤ)) (.leaf (3958905500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (1978334329148231:ℤ)) (.branch 137 (.leaf (2327506597540539:ℤ)) (.leaf (2700675100194185:ℤ)))), (.branch 124 (.leaf (1995545239197085:ℤ)) (.branch 137 (.leaf (2358488507504792:ℤ)) (.leaf (2750132087457808:ℤ)))), (.branch 124 (.leaf (1991241392007725:ℤ)) (.branch 137 (.leaf (2356577877388865:ℤ)) (.leaf (2757905047314277:ℤ)))), (.branch 124 (.leaf (2009333073561542:ℤ)) (.branch 137 (.leaf (2389691013261694:ℤ)) (.leaf (2811876399632276:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 38 17) 8000 (endpointMeanRuns 38 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 38 17, EndpointRunConditions (endpointMeanCutoff 38 17) (endpointMeanBox 38 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 38 17 h) (endpointMeanCornerA 38 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 17, endpointJoint24Q (endpointMeanCornerK 38 17 h) (endpointMeanCornerA 38 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 38 17, endpointRunWeightQ (endpointMeanCutoff 38 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 38 17) = (390344133/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 38 17 h = (logRoundedQ ((endpointMeanCutoff 38 17:ℚ)/200)).2+(390344133/1000000000000000:ℚ)+((endpointMeanRuns 38 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 38 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 38 17) r*endpointJoint24Q (endpointMeanCornerK 38 17 h) (endpointMeanCornerA 38 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 38 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 38 17 h≤endpointMeanCorner 38 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 38 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint38_17

namespace EndpointAnalyticJoint38_18
private noncomputable def weights : IntegerLookupTree := (.branch 1535 (.leaf (104580581700000:ℤ)) (.branch 2622 (.leaf (24627670100000:ℤ)) (.leaf (3941528900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (1995545239197085:ℤ)) (.branch 141 (.leaf (2358488507504792:ℤ)) (.leaf (2901828865530241:ℤ)))), (.branch 124 (.leaf (2012905878955601:ℤ)) (.branch 141 (.leaf (2389882823924113:ℤ)) (.leaf (2960505811601221:ℤ)))), (.branch 124 (.leaf (2009333073561542:ℤ)) (.branch 141 (.leaf (2389691013261694:ℤ)) (.leaf (2979339985905098:ℤ)))), (.branch 124 (.leaf (2027589129431182:ℤ)) (.branch 141 (.leaf (2423269433892500:ℤ)) (.leaf (3044038926278216:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 38 18) 8000 (endpointMeanRuns 38 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 38 18, EndpointRunConditions (endpointMeanCutoff 38 18) (endpointMeanBox 38 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 38 18 h) (endpointMeanCornerA 38 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 18, endpointJoint24Q (endpointMeanCornerK 38 18 h) (endpointMeanCornerA 38 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 38 18, endpointRunWeightQ (endpointMeanCutoff 38 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 38 18) = (194578677/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 38 18 h = (logRoundedQ ((endpointMeanCutoff 38 18:ℚ)/200)).2+(194578677/500000000000000:ℚ)+((endpointMeanRuns 38 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 38 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 38 18) r*endpointJoint24Q (endpointMeanCornerK 38 18 h) (endpointMeanCornerA 38 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 38 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 38 18 h≤endpointMeanCorner 38 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 38 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint38_18

namespace EndpointAnalyticJoint38_19
private noncomputable def weights : IntegerLookupTree := (.branch 1399 (.leaf (85393475500000:ℤ)) (.branch 2622 (.leaf (36235107300000:ℤ)) (.leaf (3922192100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2012905878955601:ℤ)) (.branch 145 (.leaf (2389882823924113:ℤ)) (.leaf (3142595109387901:ℤ)))), (.branch 124 (.leaf (2030417551026941:ℤ)) (.branch 145 (.leaf (2421695036424034:ℤ)) (.leaf (3212844766520315:ℤ)))), (.branch 124 (.leaf (2027589129431182:ℤ)) (.branch 145 (.leaf (2423269433892500:ℤ)) (.leaf (3248906487686414:ℤ)))), (.branch 124 (.leaf (2046011053060777:ℤ)) (.branch 145 (.leaf (2457319677167239:ℤ)) (.leaf (3327353826746764:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 38 19) 8000 (endpointMeanRuns 38 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 38 19, EndpointRunConditions (endpointMeanCutoff 38 19) (endpointMeanBox 38 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 38 19 h) (endpointMeanCornerA 38 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 19, endpointJoint24Q (endpointMeanCornerK 38 19 h) (endpointMeanCornerA 38 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 38 19, endpointRunWeightQ (endpointMeanCutoff 38 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 38 19) = (38783669/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 38 19 h = (logRoundedQ ((endpointMeanCutoff 38 19:ℚ)/200)).2+(38783669/100000000000000:ℚ)+((endpointMeanRuns 38 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 38 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 38 19) r*endpointJoint24Q (endpointMeanCornerK 38 19 h) (endpointMeanCornerA 38 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 38 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 38 19 h≤endpointMeanCorner 38 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 38 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint38_19

namespace EndpointAnalyticJoint38_20
private noncomputable def weights : IntegerLookupTree := (.branch 1284 (.leaf (68526882700000:ℤ)) (.branch 1967 (.leaf (32038472100000:ℤ)) (.leaf (20081694600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 132 (.leaf (2030417551026941:ℤ)) (.branch 149 (.leaf (2667943008425014:ℤ)) (.leaf (3435220093579963:ℤ)))), (.branch 132 (.leaf (2048081569346526:ℤ)) (.branch 149 (.leaf (2711150693718552:ℤ)) (.leaf (3520260692779126:ℤ)))), (.branch 132 (.leaf (2046011053060777:ℤ)) (.branch 149 (.leaf (2722009550391550:ℤ)) (.leaf (3583451023218498:ℤ)))), (.branch 132 (.leaf (2064600351463342:ℤ)) (.branch 149 (.leaf (2768868999683758:ℤ)) (.leaf (3679925930908849:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 38 20) 8000 (endpointMeanRuns 38 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 38 20, EndpointRunConditions (endpointMeanCutoff 38 20) (endpointMeanBox 38 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 38 20 h) (endpointMeanCornerA 38 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 20, endpointJoint24Q (endpointMeanCornerK 38 20 h) (endpointMeanCornerA 38 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 38 20, endpointRunWeightQ (endpointMeanCutoff 38 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 38 20) = (48334419/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 38 20 h = (logRoundedQ ((endpointMeanCutoff 38 20:ℚ)/200)).2+(48334419/125000000000000:ℚ)+((endpointMeanRuns 38 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 38 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 38 20) r*endpointJoint24Q (endpointMeanCornerK 38 20 h) (endpointMeanCornerA 38 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 38 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 38 20 h≤endpointMeanCorner 38 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 38 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint38_20

namespace EndpointAnalyticJoint38_21
private noncomputable def weights : IntegerLookupTree := (.branch 1701 (.leaf (110057890600000:ℤ)) (.branch 2622 (.leaf (14744887700000:ℤ)) (.leaf (3886261400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2048081569346526:ℤ)) (.branch 137 (.leaf (2453930707703614:ℤ)) (.leaf (2904003879030029:ℤ)))), (.branch 124 (.leaf (2065899259280621:ℤ)) (.branch 137 (.leaf (2486595474508107:ℤ)) (.leaf (2957184390394896:ℤ)))), (.branch 124 (.leaf (2064600351463342:ℤ)) (.branch 137 (.leaf (2491848372838087:ℤ)) (.leaf (2980210755779954:ℤ)))), (.branch 124 (.leaf (2083358545344051:ℤ)) (.branch 137 (.leaf (2526862243814296:ℤ)) (.leaf (3038532562340602:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 38 21) 8000 (endpointMeanRuns 38 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 38 21, EndpointRunConditions (endpointMeanCutoff 38 21) (endpointMeanBox 38 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 38 21 h) (endpointMeanCornerA 38 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 21, endpointJoint24Q (endpointMeanCornerK 38 21 h) (endpointMeanCornerA 38 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 38 21, endpointRunWeightQ (endpointMeanCutoff 38 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 38 21) = (3853827/10000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 38 21 h = (logRoundedQ ((endpointMeanCutoff 38 21:ℚ)/200)).2+(3853827/10000000000000:ℚ)+((endpointMeanRuns 38 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 38 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 38 21) r*endpointJoint24Q (endpointMeanCornerK 38 21 h) (endpointMeanCornerA 38 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 38 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 38 21 h≤endpointMeanCorner 38 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 38 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint38_21

namespace EndpointAnalyticJoint38_22
private noncomputable def weights : IntegerLookupTree := (.branch 1399 (.leaf (76463672900000:ℤ)) (.branch 2622 (.leaf (35590015000000:ℤ)) (.leaf (3869614200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2065899259280621:ℤ)) (.branch 145 (.leaf (2486595474508107:ℤ)) (.leaf (3358090272995044:ℤ)))), (.branch 124 (.leaf (2083871957725776:ℤ)) (.branch 145 (.leaf (2519695048614638:ℤ)) (.leaf (3433157114915871:ℤ)))), (.branch 124 (.leaf (2083358545344051:ℤ)) (.branch 145 (.leaf (2526862243814296:ℤ)) (.leaf (3489976754595658:ℤ)))), (.branch 124 (.leaf (2102287169224649:ℤ)) (.branch 145 (.leaf (2562368107471158:ℤ)) (.leaf (3574244920151713:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 38 22) 8000 (endpointMeanRuns 38 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 38 22, EndpointRunConditions (endpointMeanCutoff 38 22) (endpointMeanBox 38 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 38 22 h) (endpointMeanCornerA 38 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 22, endpointJoint24Q (endpointMeanCornerK 38 22 h) (endpointMeanCornerA 38 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 38 22, endpointRunWeightQ (endpointMeanCutoff 38 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 38 22) = (384245737/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 38 22 h = (logRoundedQ ((endpointMeanCutoff 38 22:ℚ)/200)).2+(384245737/1000000000000000:ℚ)+((endpointMeanRuns 38 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 38 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 38 22) r*endpointJoint24Q (endpointMeanCornerK 38 22 h) (endpointMeanCornerA 38 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 38 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 38 22 h≤endpointMeanCorner 38 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 38 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint38_22

namespace EndpointAnalyticJoint38_23
private noncomputable def weights : IntegerLookupTree := (.branch 1339 (.leaf (66789336400000:ℤ)) (.branch 2622 (.leaf (41882312400000:ℤ)) (.leaf (3851080600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2083871957725776:ℤ)) (.branch 147 (.leaf (2519695048614638:ℤ)) (.leaf (3559621414771319:ℤ)))), (.branch 124 (.leaf (2102001013209127:ℤ)) (.branch 147 (.leaf (2553235217830932:ℤ)) (.leaf (3643337035291289:ℤ)))), (.branch 124 (.leaf (2102287169224649:ℤ)) (.branch 147 (.leaf (2562368107471158:ℤ)) (.leaf (3720405704856691:ℤ)))), (.branch 124 (.leaf (2121387771568971:ℤ)) (.branch 147 (.leaf (2598372876977400:ℤ)) (.leaf (3815223940084647:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 38 23) 8000 (endpointMeanRuns 38 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 38 23, EndpointRunConditions (endpointMeanCutoff 38 23) (endpointMeanBox 38 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 38 23 h) (endpointMeanCornerA 38 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 23, endpointJoint24Q (endpointMeanCornerK 38 23 h) (endpointMeanCornerA 38 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 38 23, endpointRunWeightQ (endpointMeanCutoff 38 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 38 23) = (191489967/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 38 23 h = (logRoundedQ ((endpointMeanCutoff 38 23:ℚ)/200)).2+(191489967/500000000000000:ℚ)+((endpointMeanRuns 38 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 38 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 38 23) r*endpointJoint24Q (endpointMeanCornerK 38 23 h) (endpointMeanCornerA 38 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 38 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 38 23 h≤endpointMeanCorner 38 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 38 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint38_23

namespace EndpointAnalyticJoint38_24
private noncomputable def weights : IntegerLookupTree := (.branch 1399 (.leaf (70568189200000:ℤ)) (.branch 2622 (.leaf (35137700800000:ℤ)) (.leaf (3832748600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2102001013209127:ℤ)) (.branch 145 (.leaf (2553235217830932:ℤ)) (.leaf (3509902003076632:ℤ)))), (.branch 124 (.leaf (2120287785989601:ℤ)) (.branch 145 (.leaf (2587221847007403:ℤ)) (.leaf (3588362448568937:ℤ)))), (.branch 124 (.leaf (2121387771568971:ℤ)) (.branch 145 (.leaf (2598372876977400:ℤ)) (.leaf (3660547805198906:ℤ)))), (.branch 124 (.leaf (2140661914909619:ℤ)) (.branch 145 (.leaf (2634883562641207:ℤ)) (.leaf (3748934539599978:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 38 24) 8000 (endpointMeanRuns 38 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 38 24, EndpointRunConditions (endpointMeanCutoff 38 24) (endpointMeanBox 38 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 38 24 h) (endpointMeanCornerA 38 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 24, endpointJoint24Q (endpointMeanCornerK 38 24 h) (endpointMeanCornerA 38 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 38 24, endpointRunWeightQ (endpointMeanCutoff 38 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 38 24) = (190863949/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 38 24 h = (logRoundedQ ((endpointMeanCutoff 38 24:ℚ)/200)).2+(190863949/500000000000000:ℚ)+((endpointMeanRuns 38 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 38 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 38 24) r*endpointJoint24Q (endpointMeanCornerK 38 24 h) (endpointMeanCornerA 38 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 38 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 38 24 h≤endpointMeanCorner 38 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 38 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint38_24

namespace EndpointAnalyticJoint38_25
private noncomputable def weights : IntegerLookupTree := (.branch 1701 (.leaf (96478934100000:ℤ)) (.leaf (37423524300000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 137 (.leaf (2120287785989601:ℤ)) (.leaf (3122640901460186:ℤ))), (.branch 137 (.leaf (2138733648159959:ℤ)) (.leaf (3179825274094008:ℤ))), (.branch 137 (.leaf (2140661914909619:ℤ)) (.leaf (3220435800542058:ℤ))), (.branch 137 (.leaf (2160111175975795:ℤ)) (.leaf (3283458737237366:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 38 25) 8000 (endpointMeanRuns 38 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 38 25, EndpointRunConditions (endpointMeanCutoff 38 25) (endpointMeanBox 38 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 38 25 h) (endpointMeanCornerA 38 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 25, endpointJoint24Q (endpointMeanCornerK 38 25 h) (endpointMeanCornerA 38 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 38 25, endpointRunWeightQ (endpointMeanCutoff 38 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 38 25) = (76125259/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 38 25 h = (logRoundedQ ((endpointMeanCutoff 38 25:ℚ)/200)).2+(76125259/200000000000000:ℚ)+((endpointMeanRuns 38 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 38 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 38 25) r*endpointJoint24Q (endpointMeanCornerK 38 25 h) (endpointMeanCornerA 38 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 38 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 38 25 h≤endpointMeanCorner 38 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 38 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint38_25

namespace EndpointAnalyticJoint38_26
private noncomputable def weights : IntegerLookupTree := (.branch 1464 (.leaf (71896999100000:ℤ)) (.leaf (65486704100000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 143 (.leaf (2138733648159959:ℤ)) (.leaf (3532068253821202:ℤ))), (.branch 143 (.leaf (2157339983749753:ℤ)) (.leaf (3607148575131477:ℤ))), (.branch 143 (.leaf (2160111175975795:ℤ)) (.leaf (3682080444923443:ℤ))), (.branch 143 (.leaf (2179737145822271:ℤ)) (.leaf (3766370091944422:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 38 26) 8000 (endpointMeanRuns 38 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 38 26, EndpointRunConditions (endpointMeanCutoff 38 26) (endpointMeanBox 38 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 38 26 h) (endpointMeanCornerA 38 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 26, endpointJoint24Q (endpointMeanCornerK 38 26 h) (endpointMeanCornerA 38 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 38 26, endpointRunWeightQ (endpointMeanCutoff 38 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 38 26) = (47424933/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 38 26 h = (logRoundedQ ((endpointMeanCutoff 38 26:ℚ)/200)).2+(47424933/125000000000000:ℚ)+((endpointMeanRuns 38 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 38 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 38 26) r*endpointJoint24Q (endpointMeanCornerK 38 26 h) (endpointMeanCornerA 38 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 38 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 38 26 h≤endpointMeanCorner 38 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 38 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint38_26

namespace EndpointAnalyticJoint38_27
private noncomputable def weights : IntegerLookupTree := (.branch 1967 (.leaf (109691856100000:ℤ)) (.leaf (19376179800000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 132 (.leaf (2157339983749753:ℤ)) (.leaf (2985494769387939:ℤ))), (.branch 132 (.leaf (2176108188829174:ℤ)) (.leaf (3033845246903334:ℤ))), (.branch 132 (.leaf (2179737145822271:ℤ)) (.leaf (3067460612631167:ℤ))), (.branch 132 (.leaf (2199541429959560:ℤ)) (.leaf (3120267008924946:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 38 27) 8000 (endpointMeanRuns 38 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 38 27, EndpointRunConditions (endpointMeanCutoff 38 27) (endpointMeanBox 38 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 38 27 h) (endpointMeanCornerA 38 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 27, endpointJoint24Q (endpointMeanCornerK 38 27 h) (endpointMeanCornerA 38 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 38 27, endpointRunWeightQ (endpointMeanCutoff 38 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 38 27) = (47289977/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 38 27 h = (logRoundedQ ((endpointMeanCutoff 38 27:ℚ)/200)).2+(47289977/125000000000000:ℚ)+((endpointMeanRuns 38 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 38 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 38 27) r*endpointJoint24Q (endpointMeanCornerK 38 27 h) (endpointMeanCornerA 38 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 38 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 38 27 h≤endpointMeanCorner 38 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 38 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint38_27

namespace EndpointAnalyticJoint38_28
private noncomputable def weights : IntegerLookupTree := (.branch 1701 (.leaf (87208090600000:ℤ)) (.leaf (36819923300000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 137 (.leaf (2176108188829174:ℤ)) (.leaf (3297354818706435:ℤ))), (.branch 137 (.leaf (2195039671613810:ℤ)) (.leaf (3357738696523020:ℤ))), (.branch 137 (.leaf (2199541429959560:ℤ)) (.leaf (3413228765079924:ℤ))), (.branch 137 (.leaf (2219525648485238:ℤ)) (.leaf (3480024600709389:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 38 28) 8000 (endpointMeanRuns 38 28) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 38 28, EndpointRunConditions (endpointMeanCutoff 38 28) (endpointMeanBox 38 28).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 28, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 38 28 h) (endpointMeanCornerA 38 28 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 28, endpointJoint24Q (endpointMeanCornerK 38 28 h) (endpointMeanCornerA 38 28 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 38 28, endpointRunWeightQ (endpointMeanCutoff 38 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 38 28) = (188558597/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 38 28 h = (logRoundedQ ((endpointMeanCutoff 38 28:ℚ)/200)).2+(188558597/500000000000000:ℚ)+((endpointMeanRuns 38 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 38 28).map (fun r => endpointRunWeightQ (endpointMeanCutoff 38 28) r*endpointJoint24Q (endpointMeanCornerK 38 28 h) (endpointMeanCornerA 38 28 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 38 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 38 28 h≤endpointMeanCorner 38 28 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 38 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint38_28

namespace EndpointAnalyticJoint38_29
private noncomputable def weights : IntegerLookupTree := (.branch 1967 (.leaf (103511652400000:ℤ)) (.leaf (19196381300000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 132 (.leaf (2195039671613810:ℤ)) (.leaf (3082978766713744:ℤ))), (.branch 132 (.leaf (2206477524984377:ℤ)) (.leaf (3112840005888788:ℤ))), (.branch 132 (.leaf (2219525648485238:ℤ)) (.leaf (3173982468395620:ℤ))), (.branch 132 (.leaf (2231603227574692:ℤ)) (.leaf (3206654593458276:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 38 29) 8000 (endpointMeanRuns 38 29) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 38 29, EndpointRunConditions (endpointMeanCutoff 38 29) (endpointMeanBox 38 29).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 29, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 38 29 h) (endpointMeanCornerA 38 29 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 38 29, endpointJoint24Q (endpointMeanCornerK 38 29 h) (endpointMeanCornerA 38 29 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 38 29, endpointRunWeightQ (endpointMeanCutoff 38 29) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 38 29) = (37619043/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 38 29 h = (logRoundedQ ((endpointMeanCutoff 38 29:ℚ)/200)).2+(37619043/100000000000000:ℚ)+((endpointMeanRuns 38 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 38 29).map (fun r => endpointRunWeightQ (endpointMeanCutoff 38 29) r*endpointJoint24Q (endpointMeanCornerK 38 29 h) (endpointMeanCornerA 38 29 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 38 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 38 29 h≤endpointMeanCorner 38 29 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 38 29 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint38_29

namespace EndpointAnalyticJoint39_16
private noncomputable def weights : IntegerLookupTree := (.branch 1719 (.leaf (124493606300000:ℤ)) (.branch 2578 (.leaf (14025446400000:ℤ)) (.leaf (4400561000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (1974120105384560:ℤ)) (.branch 136 (.leaf (2325390857357923:ℤ)) (.leaf (2672803695853565:ℤ)))), (.branch 124 (.leaf (1991241392007725:ℤ)) (.branch 136 (.leaf (2356577877388865:ℤ)) (.leaf (2721451865345958:ℤ)))), (.branch 124 (.leaf (1987169959398768:ℤ)) (.branch 136 (.leaf (2355702701568974:ℤ)) (.leaf (2731330111723980:ℤ)))), (.branch 124 (.leaf (2005190424310844:ℤ)) (.branch 136 (.leaf (2389136705612320:ℤ)) (.leaf (2784630364319032:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 39 16) 8000 (endpointMeanRuns 39 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 39 16, EndpointRunConditions (endpointMeanCutoff 39 16) (endpointMeanBox 39 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 39 16 h) (endpointMeanCornerA 39 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 16, endpointJoint24Q (endpointMeanCornerK 39 16 h) (endpointMeanCornerA 39 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 39 16, endpointRunWeightQ (endpointMeanCutoff 39 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 39 16) = (388862561/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 39 16 h = (logRoundedQ ((endpointMeanCutoff 39 16:ℚ)/200)).2+(388862561/1000000000000000:ℚ)+((endpointMeanRuns 39 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 39 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 39 16) r*endpointJoint24Q (endpointMeanCornerK 39 16 h) (endpointMeanCornerA 39 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 39 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 39 16 h≤endpointMeanCorner 39 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 39 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint39_16

namespace EndpointAnalyticJoint39_17
private noncomputable def weights : IntegerLookupTree := (.branch 1547 (.leaf (103067107900000:ℤ)) (.branch 2578 (.leaf (23442749300000:ℤ)) (.leaf (4378864100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (1991241392007725:ℤ)) (.branch 140 (.leaf (2356577877388865:ℤ)) (.leaf (2874504444692174:ℤ)))), (.branch 124 (.leaf (2009333073561542:ℤ)) (.branch 140 (.leaf (2389691013261694:ℤ)) (.leaf (2935313985165720:ℤ)))), (.branch 124 (.leaf (2005190424310844:ℤ)) (.branch 140 (.leaf (2389136705612320:ℤ)) (.leaf (2954934025352598:ℤ)))), (.branch 124 (.leaf (2024239891930805:ℤ)) (.branch 140 (.leaf (2424663618642738:ℤ)) (.leaf (3022347220987838:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 39 17) 8000 (endpointMeanRuns 39 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 39 17, EndpointRunConditions (endpointMeanCutoff 39 17) (endpointMeanBox 39 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 39 17 h) (endpointMeanCornerA 39 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 17, endpointJoint24Q (endpointMeanCornerK 39 17 h) (endpointMeanCornerA 39 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 39 17, endpointRunWeightQ (endpointMeanCutoff 39 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 39 17) = (77509051/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 39 17 h = (logRoundedQ ((endpointMeanCutoff 39 17:ℚ)/200)).2+(77509051/200000000000000:ℚ)+((endpointMeanRuns 39 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 39 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 39 17) r*endpointJoint24Q (endpointMeanCornerK 39 17 h) (endpointMeanCornerA 39 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 39 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 39 17 h≤endpointMeanCorner 39 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 39 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint39_17

namespace EndpointAnalyticJoint39_18
private noncomputable def weights : IntegerLookupTree := (.branch 1719 (.leaf (116646958700000:ℤ)) (.branch 2578 (.leaf (13868479400000:ℤ)) (.leaf (4359784300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2009333073561542:ℤ)) (.branch 136 (.leaf (2389691013261694:ℤ)) (.leaf (2773354506974556:ℤ)))), (.branch 124 (.leaf (2027589129431182:ℤ)) (.branch 136 (.leaf (2423269433892500:ℤ)) (.leaf (2826247018842028:ℤ)))), (.branch 124 (.leaf (2024239891930805:ℤ)) (.branch 136 (.leaf (2424663618642738:ℤ)) (.leaf (2841571396876559:ℤ)))), (.branch 124 (.leaf (2043470330999759:ℤ)) (.branch 136 (.leaf (2460718823564737:ℤ)) (.leaf (2899676778293551:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 39 18) 8000 (endpointMeanRuns 39 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 39 18, EndpointRunConditions (endpointMeanCutoff 39 18) (endpointMeanBox 39 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 39 18 h) (endpointMeanCornerA 39 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 18, endpointJoint24Q (endpointMeanCornerK 39 18 h) (endpointMeanCornerA 39 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 39 18, endpointRunWeightQ (endpointMeanCutoff 39 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 39 18) = (386386839/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 39 18 h = (logRoundedQ ((endpointMeanCutoff 39 18:ℚ)/200)).2+(386386839/1000000000000000:ℚ)+((endpointMeanRuns 39 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 39 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 39 18) r*endpointJoint24Q (endpointMeanCornerK 39 18 h) (endpointMeanCornerA 39 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 39 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 39 18 h≤endpointMeanCorner 39 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 39 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint39_18

namespace EndpointAnalyticJoint39_19
private noncomputable def weights : IntegerLookupTree := (.branch 1719 (.leaf (112692017200000:ℤ)) (.branch 2578 (.leaf (13786726000000:ℤ)) (.leaf (4338546500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2027589129431182:ℤ)) (.branch 136 (.leaf (2423269433892500:ℤ)) (.leaf (2826247018842028:ℤ)))), (.branch 124 (.leaf (2046011053060777:ℤ)) (.branch 136 (.leaf (2457319677167239:ℤ)) (.leaf (2880148279430450:ℤ)))), (.branch 124 (.leaf (2043470330999759:ℤ)) (.branch 136 (.leaf (2460718823564737:ℤ)) (.leaf (2899676778293551:ℤ)))), (.branch 124 (.leaf (2062883460760799:ℤ)) (.branch 136 (.leaf (2497310176178314:ℤ)) (.leaf (2958970317556348:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 39 19) 8000 (endpointMeanRuns 39 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 39 19, EndpointRunConditions (endpointMeanCutoff 39 19) (endpointMeanBox 39 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 39 19 h) (endpointMeanCornerA 39 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 19, endpointJoint24Q (endpointMeanCornerK 39 19 h) (endpointMeanCornerA 39 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 39 19, endpointRunWeightQ (endpointMeanCutoff 39 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 39 19) = (77019481/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 39 19 h = (logRoundedQ ((endpointMeanCutoff 39 19:ℚ)/200)).2+(77019481/200000000000000:ℚ)+((endpointMeanRuns 39 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 39 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 39 19) r*endpointJoint24Q (endpointMeanCornerK 39 19 h) (endpointMeanCornerA 39 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 39 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 39 19 h≤endpointMeanCorner 39 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 39 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint39_19

namespace EndpointAnalyticJoint39_20
private noncomputable def weights : IntegerLookupTree := (.branch 1345 (.leaf (70780121300000:ℤ)) (.branch 2578 (.leaf (41212465200000:ℤ)) (.leaf (4317544000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2046011053060777:ℤ)) (.branch 146 (.leaf (2457319677167239:ℤ)) (.leaf (3387314889239658:ℤ)))), (.branch 124 (.leaf (2064600351463342:ℤ)) (.branch 146 (.leaf (2491848372838087:ℤ)) (.leaf (3471335590987560:ℤ)))), (.branch 124 (.leaf (2062883460760799:ℤ)) (.branch 146 (.leaf (2497310176178314:ℤ)) (.leaf (3538276561017785:ℤ)))), (.branch 124 (.leaf (2082481016789931:ℤ)) (.branch 146 (.leaf (2534445649100662:ℤ)) (.leaf (3633955591062929:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 39 20) 8000 (endpointMeanRuns 39 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 39 20, EndpointRunConditions (endpointMeanCutoff 39 20) (endpointMeanBox 39 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 39 20 h) (endpointMeanCornerA 39 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 20, endpointJoint24Q (endpointMeanCornerK 39 20 h) (endpointMeanCornerA 39 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 39 20, endpointRunWeightQ (endpointMeanCutoff 39 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 39 20) = (191911127/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 39 20 h = (logRoundedQ ((endpointMeanCutoff 39 20:ℚ)/200)).2+(191911127/500000000000000:ℚ)+((endpointMeanRuns 39 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 39 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 39 20) r*endpointJoint24Q (endpointMeanCornerK 39 20 h) (endpointMeanCornerA 39 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 39 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 39 20 h≤endpointMeanCorner 39 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 39 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint39_20

namespace EndpointAnalyticJoint39_21
private noncomputable def weights : IntegerLookupTree := (.branch 1547 (.leaf (89715778900000:ℤ)) (.branch 2210 (.leaf (17171422000000:ℤ)) (.leaf (10818976200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 128 (.leaf (2064600351463342:ℤ)) (.branch 140 (.leaf (2622293908552785:ℤ)) (.leaf (3125570516171637:ℤ)))), (.branch 128 (.leaf (2083358545344051:ℤ)) (.branch 140 (.leaf (2663072148973419:ℤ)) (.leaf (3191691306889854:ℤ)))), (.branch 128 (.leaf (2082481016789931:ℤ)) (.branch 140 (.leaf (2675316073316337:ℤ)) (.leaf (3233955650329450:ℤ)))), (.branch 128 (.leaf (2102264751151301:ℤ)) (.branch 140 (.leaf (2719509953138802:ℤ)) (.leaf (3307734382125452:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 39 21) 8000 (endpointMeanRuns 39 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 39 21, EndpointRunConditions (endpointMeanCutoff 39 21) (endpointMeanBox 39 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 39 21 h) (endpointMeanCornerA 39 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 21, endpointJoint24Q (endpointMeanCornerK 39 21 h) (endpointMeanCornerA 39 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 39 21, endpointRunWeightQ (endpointMeanCutoff 39 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 39 21) = (95675131/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 39 21 h = (logRoundedQ ((endpointMeanCutoff 39 21:ℚ)/200)).2+(95675131/250000000000000:ℚ)+((endpointMeanRuns 39 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 39 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 39 21) r*endpointJoint24Q (endpointMeanCornerK 39 21 h) (endpointMeanCornerA 39 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 39 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 39 21 h≤endpointMeanCorner 39 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 39 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint39_21

namespace EndpointAnalyticJoint39_22
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.leaf (79185220300000:ℤ)) (.branch 2578 (.leaf (28171240600000:ℤ)) (.leaf (4278496400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2083358545344051:ℤ)) (.branch 142 (.leaf (2526862243814296:ℤ)) (.leaf (3303866577945369:ℤ)))), (.branch 124 (.leaf (2102287169224649:ℤ)) (.branch 142 (.leaf (2562368107471158:ℤ)) (.leaf (3377524944028707:ℤ)))), (.branch 124 (.leaf (2102264751151301:ℤ)) (.branch 142 (.leaf (2572133333503318:ℤ)) (.leaf (3436271514785238:ℤ)))), (.branch 124 (.leaf (2122236432553783:ℤ)) (.branch 142 (.leaf (2610381440875050:ℤ)) (.leaf (3519161655913201:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 39 22) 8000 (endpointMeanRuns 39 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 39 22, EndpointRunConditions (endpointMeanCutoff 39 22) (endpointMeanBox 39 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 39 22 h) (endpointMeanCornerA 39 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 22, endpointJoint24Q (endpointMeanCornerK 39 22 h) (endpointMeanCornerA 39 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 39 22, endpointRunWeightQ (endpointMeanCutoff 39 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 39 22) = (381451507/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 39 22 h = (logRoundedQ ((endpointMeanCutoff 39 22:ℚ)/200)).2+(381451507/1000000000000000:ℚ)+((endpointMeanRuns 39 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 39 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 39 22) r*endpointJoint24Q (endpointMeanCornerK 39 22 h) (endpointMeanCornerA 39 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 39 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 39 22 h≤endpointMeanCorner 39 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 39 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint39_22

namespace EndpointAnalyticJoint39_23
private noncomputable def weights : IntegerLookupTree := (.branch 1673 (.leaf (94625988200000:ℤ)) (.leaf (39960355100000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 137 (.leaf (2102287169224649:ℤ)) (.leaf (3097995708692033:ℤ))), (.branch 137 (.leaf (2121387771568971:ℤ)) (.leaf (3158622530502418:ℤ))), (.branch 137 (.leaf (2122236432553783:ℤ)) (.leaf (3200300345049404:ℤ))), (.branch 137 (.leaf (2142397846509128:ℤ)) (.leaf (3267541637822944:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 39 23) 8000 (endpointMeanRuns 39 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 39 23, EndpointRunConditions (endpointMeanCutoff 39 23) (endpointMeanBox 39 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 39 23 h) (endpointMeanCornerA 39 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 23, endpointJoint24Q (endpointMeanCornerK 39 23 h) (endpointMeanCornerA 39 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 39 23, endpointRunWeightQ (endpointMeanCutoff 39 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 39 23) = (380215897/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 39 23 h = (logRoundedQ ((endpointMeanCutoff 39 23:ℚ)/200)).2+(380215897/1000000000000000:ℚ)+((endpointMeanRuns 39 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 39 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 39 23) r*endpointJoint24Q (endpointMeanCornerK 39 23 h) (endpointMeanCornerA 39 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 39 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 39 23 h≤endpointMeanCorner 39 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 39 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint39_23

namespace EndpointAnalyticJoint39_24
private noncomputable def weights : IntegerLookupTree := (.branch 1673 (.leaf (91713484200000:ℤ)) (.leaf (39758782900000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 137 (.leaf (2121387771568971:ℤ)) (.leaf (3158622530502418:ℤ))), (.branch 137 (.leaf (2140661914909619:ℤ)) (.leaf (3220435800542058:ℤ))), (.branch 137 (.leaf (2142397846509128:ℤ)) (.leaf (3267541637822944:ℤ))), (.branch 137 (.leaf (2162750795491608:ℤ)) (.leaf (3336195732823266:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 39 24) 8000 (endpointMeanRuns 39 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 39 24, EndpointRunConditions (endpointMeanCutoff 39 24) (endpointMeanBox 39 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 39 24 h) (endpointMeanCornerA 39 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 24, endpointJoint24Q (endpointMeanCornerK 39 24 h) (endpointMeanCornerA 39 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 39 24, endpointRunWeightQ (endpointMeanCutoff 39 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 39 24) = (379128601/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 39 24 h = (logRoundedQ ((endpointMeanCutoff 39 24:ℚ)/200)).2+(379128601/1000000000000000:ℚ)+((endpointMeanRuns 39 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 39 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 39 24) r*endpointJoint24Q (endpointMeanCornerK 39 24 h) (endpointMeanCornerA 39 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 39 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 39 24 h≤endpointMeanCorner 39 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 39 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint39_24

namespace EndpointAnalyticJoint39_25
private noncomputable def weights : IntegerLookupTree := (.branch 1673 (.leaf (88540107000000:ℤ)) (.leaf (39534267000000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 137 (.leaf (2140661914909619:ℤ)) (.leaf (3220435800542058:ℤ))), (.branch 137 (.leaf (2160111175975795:ℤ)) (.leaf (3283458737237366:ℤ))), (.branch 137 (.leaf (2162750795491608:ℤ)) (.leaf (3336195732823266:ℤ))), (.branch 137 (.leaf (2183297099099115:ℤ)) (.leaf (3406292314341821:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 39 25) 8000 (endpointMeanRuns 39 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 39 25, EndpointRunConditions (endpointMeanCutoff 39 25) (endpointMeanBox 39 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 39 25 h) (endpointMeanCornerA 39 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 25, endpointJoint24Q (endpointMeanCornerK 39 25 h) (endpointMeanCornerA 39 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 39 25, endpointRunWeightQ (endpointMeanCutoff 39 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 39 25) = (47239693/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 39 25 h = (logRoundedQ ((endpointMeanCutoff 39 25:ℚ)/200)).2+(47239693/125000000000000:ℚ)+((endpointMeanRuns 39 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 39 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 39 25) r*endpointJoint24Q (endpointMeanCornerK 39 25 h) (endpointMeanCornerA 39 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 39 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 39 25 h≤endpointMeanCorner 39 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 39 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint39_25

namespace EndpointAnalyticJoint39_26
private noncomputable def weights : IntegerLookupTree := (.branch 1673 (.leaf (85472363500000:ℤ)) (.leaf (39312088400000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 137 (.leaf (2160111175975795:ℤ)) (.leaf (3283458737237366:ℤ))), (.branch 137 (.leaf (2179737145822271:ℤ)) (.leaf (3347715013392208:ℤ))), (.branch 137 (.leaf (2183297099099115:ℤ)) (.leaf (3406292314341821:ℤ))), (.branch 137 (.leaf (2204038594215892:ℤ)) (.leaf (3477861690364675:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 39 26) 8000 (endpointMeanRuns 39 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 39 26, EndpointRunConditions (endpointMeanCutoff 39 26) (endpointMeanBox 39 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 39 26 h) (endpointMeanCornerA 39 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 26, endpointJoint24Q (endpointMeanCornerK 39 26 h) (endpointMeanCornerA 39 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 39 26, endpointRunWeightQ (endpointMeanCutoff 39 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 39 26) = (47089887/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 39 26 h = (logRoundedQ ((endpointMeanCutoff 39 26:ℚ)/200)).2+(47089887/125000000000000:ℚ)+((endpointMeanRuns 39 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 39 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 39 26) r*endpointJoint24Q (endpointMeanCornerK 39 26 h) (endpointMeanCornerA 39 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 39 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 39 26 h≤endpointMeanCorner 39 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 39 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint39_26

namespace EndpointAnalyticJoint39_27
private noncomputable def weights : IntegerLookupTree := (.branch 1673 (.leaf (82831222300000:ℤ)) (.leaf (39116519700000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 137 (.leaf (2179737145822271:ℤ)) (.leaf (3347715013392208:ℤ))), (.branch 137 (.leaf (2199541429959560:ℤ)) (.leaf (3413228765079924:ℤ))), (.branch 137 (.leaf (2204038594215892:ℤ)) (.leaf (3477861690364675:ℤ))), (.branch 137 (.leaf (2224977135176701:ℤ)) (.leaf (3550934805676947:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 39 27) 8000 (endpointMeanRuns 39 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 39 27, EndpointRunConditions (endpointMeanCutoff 39 27) (endpointMeanBox 39 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 39 27 h) (endpointMeanCornerA 39 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 27, endpointJoint24Q (endpointMeanCornerK 39 27 h) (endpointMeanCornerA 39 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 39 27, endpointRunWeightQ (endpointMeanCutoff 39 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 39 27) = (187832091/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 39 27 h = (logRoundedQ ((endpointMeanCutoff 39 27:ℚ)/200)).2+(187832091/500000000000000:ℚ)+((endpointMeanRuns 39 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 39 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 39 27) r*endpointJoint24Q (endpointMeanCornerK 39 27 h) (endpointMeanCornerA 39 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 39 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 39 27 h≤endpointMeanCorner 39 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 39 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint39_27

namespace EndpointAnalyticJoint39_28
private noncomputable def weights : IntegerLookupTree := (.branch 2210 (.leaf (114197636300000:ℤ)) (.leaf (10457015500000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 128 (.leaf (2199541429959560:ℤ)) (.leaf (2921408792465720:ℤ))), (.branch 128 (.leaf (2219525648485238:ℤ)) (.leaf (2966838448431269:ℤ))), (.branch 128 (.leaf (2224977135176701:ℤ)) (.leaf (3000433291750667:ℤ))), (.branch 128 (.leaf (2246114593932657:ℤ)) (.leaf (3049997823446016:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 39 28) 8000 (endpointMeanRuns 39 28) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 39 28, EndpointRunConditions (endpointMeanCutoff 39 28) (endpointMeanBox 39 28).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 28, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 39 28 h) (endpointMeanCornerA 39 28 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 28, endpointJoint24Q (endpointMeanCornerK 39 28 h) (endpointMeanCornerA 39 28 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 39 28, endpointRunWeightQ (endpointMeanCutoff 39 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 39 28) = (187244423/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 39 28 h = (logRoundedQ ((endpointMeanCutoff 39 28:ℚ)/200)).2+(187244423/500000000000000:ℚ)+((endpointMeanRuns 39 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 39 28).map (fun r => endpointRunWeightQ (endpointMeanCutoff 39 28) r*endpointJoint24Q (endpointMeanCornerK 39 28 h) (endpointMeanCornerA 39 28 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 39 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 39 28 h≤endpointMeanCorner 39 28 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 39 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint39_28

namespace EndpointAnalyticJoint39_29
private noncomputable def weights : IntegerLookupTree := (.branch 1673 (.leaf (77780952100000:ℤ)) (.leaf (38730677900000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 137 (.leaf (2219525648485238:ℤ)) (.leaf (3480024600709389:ℤ))), (.branch 137 (.leaf (2231603227574692:ℤ)) (.leaf (3520727919499359:ℤ))), (.branch 137 (.leaf (2246114593932657:ℤ)) (.leaf (3625543255242508:ℤ))), (.branch 137 (.leaf (2258893335112714:ℤ)) (.leaf (3671058677054232:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 39 29) 8000 (endpointMeanRuns 39 29) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 39 29, EndpointRunConditions (endpointMeanCutoff 39 29) (endpointMeanBox 39 29).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 29, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 39 29 h) (endpointMeanCornerA 39 29 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 29, endpointJoint24Q (endpointMeanCornerK 39 29 h) (endpointMeanCornerA 39 29 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 39 29, endpointRunWeightQ (endpointMeanCutoff 39 29) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 39 29) = (373582921/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 39 29 h = (logRoundedQ ((endpointMeanCutoff 39 29:ℚ)/200)).2+(373582921/1000000000000000:ℚ)+((endpointMeanRuns 39 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 39 29).map (fun r => endpointRunWeightQ (endpointMeanCutoff 39 29) r*endpointJoint24Q (endpointMeanCornerK 39 29 h) (endpointMeanCornerA 39 29 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 39 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 39 29 h≤endpointMeanCorner 39 29 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 39 29 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint39_29

namespace EndpointAnalyticJoint39_30
private noncomputable def weights : IntegerLookupTree := (.branch 1407 (.leaf (54317632500000:ℤ)) (.branch 2578 (.leaf (32688383400000:ℤ)) (.leaf (4140421900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2231603227574692:ℤ)) (.branch 144 (.leaf (2809552918197398:ℤ)) (.leaf (4086956417215412:ℤ)))), (.branch 124 (.leaf (2239691436216497:ℤ)) (.branch 144 (.leaf (2825278067475600:ℤ)) (.leaf (4125120133635494:ℤ)))), (.branch 124 (.leaf (2258893335112714:ℤ)) (.branch 144 (.leaf (2877486155231051:ℤ)) (.leaf (4332404834815519:ℤ)))), (.branch 124 (.leaf (2267452860218539:ℤ)) (.branch 144 (.leaf (2894525906295481:ℤ)) (.leaf (4376308309053756:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 39 30) 8000 (endpointMeanRuns 39 30) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 39 30, EndpointRunConditions (endpointMeanCutoff 39 30) (endpointMeanBox 39 30).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 30, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 39 30 h) (endpointMeanCornerA 39 30 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 30, endpointJoint24Q (endpointMeanCornerK 39 30 h) (endpointMeanCornerA 39 30 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 39 30, endpointRunWeightQ (endpointMeanCutoff 39 30) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 39 30) = (373068433/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 39 30 h = (logRoundedQ ((endpointMeanCutoff 39 30:ℚ)/200)).2+(373068433/1000000000000000:ℚ)+((endpointMeanRuns 39 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 39 30).map (fun r => endpointRunWeightQ (endpointMeanCutoff 39 30) r*endpointJoint24Q (endpointMeanCornerK 39 30 h) (endpointMeanCornerA 39 30 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 39 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 39 30 h≤endpointMeanCorner 39 30 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 39 30 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint39_30

namespace EndpointAnalyticJoint39_31
private noncomputable def weights : IntegerLookupTree := (.branch 1407 (.leaf (52595426800000:ℤ)) (.branch 2578 (.leaf (32532198600000:ℤ)) (.leaf (4125683000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2239691436216497:ℤ)) (.branch 144 (.leaf (2825278067475600:ℤ)) (.leaf (4125120133635494:ℤ)))), (.branch 124 (.leaf (2260040442823871:ℤ)) (.branch 144 (.leaf (2864977080788288:ℤ)) (.leaf (4222095832033538:ℤ)))), (.branch 124 (.leaf (2267452860218539:ℤ)) (.branch 144 (.leaf (2894525906295481:ℤ)) (.leaf (4376308309053756:ℤ)))), (.branch 124 (.leaf (2288993841721760:ℤ)) (.branch 144 (.leaf (2937568051977516:ℤ)) (.leaf (4488023335537571:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 39 31) 8000 (endpointMeanRuns 39 31) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 39 31, EndpointRunConditions (endpointMeanCutoff 39 31) (endpointMeanBox 39 31).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 31, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 39 31 h) (endpointMeanCornerA 39 31 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 39 31, endpointJoint24Q (endpointMeanCornerK 39 31 h) (endpointMeanCornerA 39 31 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 39 31, endpointRunWeightQ (endpointMeanCutoff 39 31) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 39 31) = (186086787/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 39 31 h = (logRoundedQ ((endpointMeanCutoff 39 31:ℚ)/200)).2+(186086787/500000000000000:ℚ)+((endpointMeanRuns 39 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 39 31).map (fun r => endpointRunWeightQ (endpointMeanCutoff 39 31) r*endpointJoint24Q (endpointMeanCornerK 39 31 h) (endpointMeanCornerA 39 31 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 39 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 39 31 h≤endpointMeanCorner 39 31 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 39 31 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint39_31

namespace EndpointAnalyticJoint40_16
private noncomputable def weights : IntegerLookupTree := (.branch 1353 (.leaf (77156533800000:ℤ)) (.branch 2536 (.leaf (40481914100000:ℤ)) (.leaf (4831483100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2002821880417563:ℤ)) (.branch 145 (.leaf (2384732600241768:ℤ)) (.leaf (3198171614184764:ℤ)))), (.branch 124 (.leaf (2005190424310844:ℤ)) (.branch 145 (.leaf (2389136705612320:ℤ)) (.leaf (3208554755783565:ℤ)))), (.branch 124 (.leaf (2017835613618580:ℤ)) (.branch 145 (.leaf (2421202730681171:ℤ)) (.leaf (3336623817044325:ℤ)))), (.branch 124 (.leaf (2020333676549727:ℤ)) (.branch 145 (.leaf (2425946911218630:ℤ)) (.leaf (3348507478688715:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 40 16) 8000 (endpointMeanRuns 40 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 40 16, EndpointRunConditions (endpointMeanCutoff 40 16) (endpointMeanBox 40 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 40 16 h) (endpointMeanCornerA 40 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 16, endpointJoint24Q (endpointMeanCornerK 40 16 h) (endpointMeanCornerA 40 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 40 16, endpointRunWeightQ (endpointMeanCutoff 40 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 40 16) = (192762807/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 40 16 h = (logRoundedQ ((endpointMeanCutoff 40 16:ℚ)/200)).2+(192762807/500000000000000:ℚ)+((endpointMeanRuns 40 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 40 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 40 16) r*endpointJoint24Q (endpointMeanCornerK 40 16 h) (endpointMeanCornerA 40 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 40 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 40 16 h≤endpointMeanCorner 40 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 40 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint40_16

namespace EndpointAnalyticJoint40_17
private noncomputable def weights : IntegerLookupTree := (.branch 1218 (.leaf (58416139400000:ℤ)) (.branch 1902 (.leaf (38346919400000:ℤ)) (.leaf (23375412600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 132 (.leaf (2005190424310844:ℤ)) (.branch 150 (.leaf (2636342990462495:ℤ)) (.leaf (3525506708144371:ℤ)))), (.branch 132 (.leaf (2024239891930805:ℤ)) (.branch 150 (.leaf (2684762576236860:ℤ)) (.leaf (3632879537612193:ℤ)))), (.branch 132 (.leaf (2020333676549727:ℤ)) (.branch 150 (.leaf (2694806601991034:ℤ)) (.leaf (3735039863103868:ℤ)))), (.branch 132 (.leaf (2040429835084342:ℤ)) (.branch 150 (.leaf (2747842973406028:ℤ)) (.leaf (3861887484935475:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 40 17) 8000 (endpointMeanRuns 40 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 40 17, EndpointRunConditions (endpointMeanCutoff 40 17) (endpointMeanBox 40 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 40 17 h) (endpointMeanCornerA 40 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 17, endpointJoint24Q (endpointMeanCornerK 40 17 h) (endpointMeanCornerA 40 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 40 17, endpointRunWeightQ (endpointMeanCutoff 40 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 40 17) = (76962563/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 40 17 h = (logRoundedQ ((endpointMeanCutoff 40 17:ℚ)/200)).2+(76962563/200000000000000:ℚ)+((endpointMeanRuns 40 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 40 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 40 17) r*endpointJoint24Q (endpointMeanCornerK 40 17 h) (endpointMeanCornerA 40 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 40 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 40 17 h≤endpointMeanCorner 40 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 40 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint40_17

namespace EndpointAnalyticJoint40_18
private noncomputable def weights : IntegerLookupTree := (.branch 1242 (.leaf (58870315800000:ℤ)) (.branch 1902 (.leaf (35153659800000:ℤ)) (.leaf (23247610300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 132 (.leaf (2024239891930805:ℤ)) (.branch 149 (.leaf (2684762576236860:ℤ)) (.leaf (3557873796081689:ℤ)))), (.branch 132 (.leaf (2043470330999759:ℤ)) (.branch 149 (.leaf (2734071445497872:ℤ)) (.leaf (3663002958175029:ℤ)))), (.branch 132 (.leaf (2040429835084342:ℤ)) (.branch 149 (.leaf (2747842973406028:ℤ)) (.leaf (3767994759487863:ℤ)))), (.branch 132 (.leaf (2060725889107777:ℤ)) (.branch 149 (.leaf (2801923151337888:ℤ)) (.leaf (3891718790377264:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 40 18) 8000 (endpointMeanRuns 40 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 40 18, EndpointRunConditions (endpointMeanCutoff 40 18) (endpointMeanBox 40 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 40 18 h) (endpointMeanCornerA 40 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 18, endpointJoint24Q (endpointMeanCornerK 40 18 h) (endpointMeanCornerA 40 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 40 18, endpointRunWeightQ (endpointMeanCutoff 40 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 40 18) = (76708159/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 40 18 h = (logRoundedQ ((endpointMeanCutoff 40 18:ℚ)/200)).2+(76708159/200000000000000:ℚ)+((endpointMeanRuns 40 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 40 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 40 18) r*endpointJoint24Q (endpointMeanCornerK 40 18 h) (endpointMeanCornerA 40 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 40 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 40 18 h≤endpointMeanCorner 40 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 40 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint40_18

namespace EndpointAnalyticJoint40_19
private noncomputable def weights : IntegerLookupTree := (.branch 1416 (.leaf (76525657100000:ℤ)) (.branch 2536 (.leaf (33264365500000:ℤ)) (.leaf (4771718800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2043470330999759:ℤ)) (.branch 143 (.leaf (2460718823564737:ℤ)) (.leaf (3256562228177111:ℤ)))), (.branch 124 (.leaf (2062883460760799:ℤ)) (.branch 143 (.leaf (2497310176178314:ℤ)) (.leaf (3337363640248082:ℤ)))), (.branch 124 (.leaf (2060725889107777:ℤ)) (.branch 143 (.leaf (2503130513038143:ℤ)) (.leaf (3398524454266237:ℤ)))), (.branch 124 (.leaf (2081223826970509:ℤ)) (.branch 143 (.leaf (2542638361906464:ℤ)) (.leaf (3490678610065309:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 40 19) 8000 (endpointMeanRuns 40 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 40 19, EndpointRunConditions (endpointMeanCutoff 40 19) (endpointMeanBox 40 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 40 19 h) (endpointMeanCornerA 40 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 19, endpointJoint24Q (endpointMeanCornerK 40 19 h) (endpointMeanCornerA 40 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 40 19, endpointRunWeightQ (endpointMeanCutoff 40 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 40 19) = (191141339/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 40 19 h = (logRoundedQ ((endpointMeanCutoff 40 19:ℚ)/200)).2+(191141339/500000000000000:ℚ)+((endpointMeanRuns 40 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 40 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 40 19) r*endpointJoint24Q (endpointMeanCornerK 40 19 h) (endpointMeanCornerA 40 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 40 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 40 19 h≤endpointMeanCorner 40 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 40 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint40_19

namespace EndpointAnalyticJoint40_20
private noncomputable def weights : IntegerLookupTree := (.branch 1268 (.leaf (57110118800000:ℤ)) (.branch 2536 (.leaf (50229366400000:ℤ)) (.leaf (4751319700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2062883460760799:ℤ)) (.branch 148 (.leaf (2497310176178314:ℤ)) (.leaf (3689513017198442:ℤ)))), (.branch 124 (.leaf (2082481016789931:ℤ)) (.branch 148 (.leaf (2534445649100662:ℤ)) (.leaf (3795321786457667:ℤ)))), (.branch 124 (.leaf (2081223826970509:ℤ)) (.branch 148 (.leaf (2542638361906464:ℤ)) (.leaf (3917422307001198:ℤ)))), (.branch 124 (.leaf (2101925656801037:ℤ)) (.branch 148 (.leaf (2582769777989552:ℤ)) (.leaf (4041862319364594:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 40 20) 8000 (endpointMeanRuns 40 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 40 20, EndpointRunConditions (endpointMeanCutoff 40 20) (endpointMeanBox 40 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 40 20 h) (endpointMeanCornerA 40 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 20, endpointJoint24Q (endpointMeanCornerK 40 20 h) (endpointMeanCornerA 40 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 40 20, endpointRunWeightQ (endpointMeanCutoff 40 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 40 20) = (381175779/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 40 20 h = (logRoundedQ ((endpointMeanCutoff 40 20:ℚ)/200)).2+(381175779/1000000000000000:ℚ)+((endpointMeanRuns 40 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 40 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 40 20) r*endpointJoint24Q (endpointMeanCornerK 40 20 h) (endpointMeanCornerA 40 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 40 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 40 20 h≤endpointMeanCorner 40 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 40 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint40_20

namespace EndpointAnalyticJoint40_21
private noncomputable def weights : IntegerLookupTree := (.branch 1485 (.leaf (78071247000000:ℤ)) (.branch 2536 (.leaf (26921727900000:ℤ)) (.leaf (4728602800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2082481016789931:ℤ)) (.branch 141 (.leaf (2534445649100662:ℤ)) (.leaf (3293327835717979:ℤ)))), (.branch 124 (.leaf (2102264751151301:ℤ)) (.branch 141 (.leaf (2572133333503318:ℤ)) (.leaf (3370577852304717:ℤ)))), (.branch 124 (.leaf (2101925656801037:ℤ)) (.branch 141 (.leaf (2582769777989552:ℤ)) (.leaf (3435775509389320:ℤ)))), (.branch 124 (.leaf (2122833406702626:ℤ)) (.branch 141 (.leaf (2623534603282914:ℤ)) (.leaf (3523464360333483:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 40 21) 8000 (endpointMeanRuns 40 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 40 21, EndpointRunConditions (endpointMeanCutoff 40 21) (endpointMeanBox 40 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 40 21 h) (endpointMeanCornerA 40 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 21, endpointJoint24Q (endpointMeanCornerK 40 21 h) (endpointMeanCornerA 40 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 40 21, endpointRunWeightQ (endpointMeanCutoff 40 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 40 21) = (379943109/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 40 21 h = (logRoundedQ ((endpointMeanCutoff 40 21:ℚ)/200)).2+(379943109/1000000000000000:ℚ)+((endpointMeanRuns 40 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 40 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 40 21) r*endpointJoint24Q (endpointMeanCornerK 40 21 h) (endpointMeanCornerA 40 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 40 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 40 21 h≤endpointMeanCorner 40 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 40 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint40_21

namespace EndpointAnalyticJoint40_22
private noncomputable def weights : IntegerLookupTree := (.branch 1295 (.leaf (55225788700000:ℤ)) (.branch 2536 (.leaf (45983776700000:ℤ)) (.leaf (4706126500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2102264751151301:ℤ)) (.branch 147 (.leaf (2572133333503318:ℤ)) (.leaf (3815911572869452:ℤ)))), (.branch 124 (.leaf (2122236432553783:ℤ)) (.branch 147 (.leaf (2610381440875050:ℤ)) (.leaf (3922159083561904:ℤ)))), (.branch 124 (.leaf (2122833406702626:ℤ)) (.branch 147 (.leaf (2623534603282914:ℤ)) (.leaf (4060304317167824:ℤ)))), (.branch 124 (.leaf (2143949124951966:ℤ)) (.branch 147 (.leaf (2664942835121986:ℤ)) (.leaf (4185149294176754:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 40 22) 8000 (endpointMeanRuns 40 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 40 22, EndpointRunConditions (endpointMeanCutoff 40 22) (endpointMeanBox 40 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 40 22 h) (endpointMeanCornerA 40 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 22, endpointJoint24Q (endpointMeanCornerK 40 22 h) (endpointMeanCornerA 40 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 40 22, endpointRunWeightQ (endpointMeanCutoff 40 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 40 22) = (189361749/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 40 22 h = (logRoundedQ ((endpointMeanCutoff 40 22:ℚ)/200)).2+(189361749/500000000000000:ℚ)+((endpointMeanRuns 40 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 40 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 40 22) r*endpointJoint24Q (endpointMeanCornerK 40 22 h) (endpointMeanCornerA 40 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 40 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 40 22 h≤endpointMeanCorner 40 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 40 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint40_22

namespace EndpointAnalyticJoint40_23
private noncomputable def weights : IntegerLookupTree := (.branch 1323 (.leaf (55880599900000:ℤ)) (.branch 2536 (.leaf (42246470900000:ℤ)) (.leaf (4683885900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2122236432553783:ℤ)) (.branch 146 (.leaf (2610381440875050:ℤ)) (.leaf (3833145423875639:ℤ)))), (.branch 124 (.leaf (2142397846509128:ℤ)) (.branch 146 (.leaf (2649198304811016:ℤ)) (.leaf (3936798043972950:ℤ)))), (.branch 124 (.leaf (2143949124951966:ℤ)) (.branch 146 (.leaf (2664942835121986:ℤ)) (.leaf (4075015420125352:ℤ)))), (.branch 124 (.leaf (2165274880199868:ℤ)) (.branch 146 (.leaf (2707004628633872:ℤ)) (.leaf (4196357561153422:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 40 23) 8000 (endpointMeanRuns 40 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 40 23, EndpointRunConditions (endpointMeanCutoff 40 23) (endpointMeanBox 40 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 40 23 h) (endpointMeanCornerA 40 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 23, endpointJoint24Q (endpointMeanCornerK 40 23 h) (endpointMeanCornerA 40 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 40 23, endpointRunWeightQ (endpointMeanCutoff 40 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 40 23) = (377516673/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 40 23 h = (logRoundedQ ((endpointMeanCutoff 40 23:ℚ)/200)).2+(377516673/1000000000000000:ℚ)+((endpointMeanRuns 40 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 40 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 40 23) r*endpointJoint24Q (endpointMeanCornerK 40 23 h) (endpointMeanCornerA 40 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 40 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 40 23 h≤endpointMeanCorner 40 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 40 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint40_23

namespace EndpointAnalyticJoint40_24
private noncomputable def weights : IntegerLookupTree := (.branch 2536 (.leaf (137515726100000:ℤ)) (.leaf (4661876000000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2142397846509128:ℤ)) (.leaf (2649198304811016:ℤ))), (.branch 124 (.leaf (2162750795491608:ℤ)) (.leaf (2688592382828508:ℤ))), (.branch 124 (.leaf (2165274880199868:ℤ)) (.leaf (2707004628633872:ℤ))), (.branch 124 (.leaf (2186812761673896:ℤ)) (.leaf (2749730299227900:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 40 24) 8000 (endpointMeanRuns 40 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 40 24, EndpointRunConditions (endpointMeanCutoff 40 24) (endpointMeanBox 40 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 40 24 h) (endpointMeanCornerA 40 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 24, endpointJoint24Q (endpointMeanCornerK 40 24 h) (endpointMeanCornerA 40 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 40 24, endpointRunWeightQ (endpointMeanCutoff 40 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 40 24) = (376322369/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 40 24 h = (logRoundedQ ((endpointMeanCutoff 40 24:ℚ)/200)).2+(376322369/1000000000000000:ℚ)+((endpointMeanRuns 40 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 40 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 40 24) r*endpointJoint24Q (endpointMeanCornerK 40 24 h) (endpointMeanCornerA 40 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 40 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 40 24 h≤endpointMeanCorner 40 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 40 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint40_24

namespace EndpointAnalyticJoint40_25
private noncomputable def weights : IntegerLookupTree := (.branch 1691 (.leaf (84392070600000:ℤ)) (.leaf (37368010600000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 136 (.leaf (2162750795491608:ℤ)) (.leaf (3274128339088139:ℤ))), (.branch 136 (.leaf (2183297099099115:ℤ)) (.leaf (3341078786351230:ℤ))), (.branch 136 (.leaf (2186812761673896:ℤ)) (.leaf (3404597663637901:ℤ))), (.branch 136 (.leaf (2208564879383070:ℤ)) (.leaf (3479650448985866:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 40 25) 8000 (endpointMeanRuns 40 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 40 25, EndpointRunConditions (endpointMeanCutoff 40 25) (endpointMeanBox 40 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 40 25 h) (endpointMeanCornerA 40 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 25, endpointJoint24Q (endpointMeanCornerK 40 25 h) (endpointMeanCornerA 40 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 40 25, endpointRunWeightQ (endpointMeanCutoff 40 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 40 25) = (375140329/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 40 25 h = (logRoundedQ ((endpointMeanCutoff 40 25:ℚ)/200)).2+(375140329/1000000000000000:ℚ)+((endpointMeanRuns 40 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 40 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 40 25) r*endpointJoint24Q (endpointMeanCornerK 40 25 h) (endpointMeanCornerA 40 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 40 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 40 25 h≤endpointMeanCorner 40 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 40 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint40_25

namespace EndpointAnalyticJoint40_26
private noncomputable def weights : IntegerLookupTree := (.branch 2536 (.leaf (129946634200000:ℤ)) (.leaf (4620914700000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2183297099099115:ℤ)) (.leaf (2728572258209688:ℤ))), (.branch 124 (.leaf (2204038594215892:ℤ)) (.leaf (2769146641871749:ℤ))), (.branch 124 (.leaf (2208564879383070:ℤ)) (.leaf (2793130325125347:ℤ))), (.branch 124 (.leaf (2230533364324565:ℤ)) (.leaf (2837215349929210:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 40 26) 8000 (endpointMeanRuns 40 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 40 26, EndpointRunConditions (endpointMeanCutoff 40 26) (endpointMeanBox 40 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 40 26 h) (endpointMeanCornerA 40 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 26, endpointJoint24Q (endpointMeanCornerK 40 26 h) (endpointMeanCornerA 40 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 40 26, endpointRunWeightQ (endpointMeanCutoff 40 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 40 26) = (374099719/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 40 26 h = (logRoundedQ ((endpointMeanCutoff 40 26:ℚ)/200)).2+(374099719/1000000000000000:ℚ)+((endpointMeanRuns 40 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 40 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 40 26) r*endpointJoint24Q (endpointMeanCornerK 40 26 h) (endpointMeanCornerA 40 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 40 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 40 26 h≤endpointMeanCorner 40 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 40 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint40_26

namespace EndpointAnalyticJoint40_27
private noncomputable def weights : IntegerLookupTree := (.branch 2536 (.leaf (126113417400000:ℤ)) (.leaf (4599545300000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2204038594215892:ℤ)) (.leaf (2769146641871749:ℤ))), (.branch 124 (.leaf (2224977135176701:ℤ)) (.leaf (2810324374264848:ℤ))), (.branch 124 (.leaf (2230533364324565:ℤ)) (.leaf (2837215349929210:ℤ))), (.branch 124 (.leaf (2252720368692461:ℤ)) (.leaf (2881996185234453:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 40 27) 8000 (endpointMeanRuns 40 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 40 27, EndpointRunConditions (endpointMeanCutoff 40 27) (endpointMeanBox 40 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 40 27 h) (endpointMeanCornerA 40 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 27, endpointJoint24Q (endpointMeanCornerK 40 27 h) (endpointMeanCornerA 40 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 40 27, endpointRunWeightQ (endpointMeanCutoff 40 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 40 27) = (372940169/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 40 27 h = (logRoundedQ ((endpointMeanCutoff 40 27:ℚ)/200)).2+(372940169/1000000000000000:ℚ)+((endpointMeanRuns 40 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 40 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 40 27) r*endpointJoint24Q (endpointMeanCornerK 40 27 h) (endpointMeanCornerA 40 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 40 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 40 27 h≤endpointMeanCorner 40 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 40 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint40_27

namespace EndpointAnalyticJoint40_28
private noncomputable def weights : IntegerLookupTree := (.branch 2536 (.leaf (122395699000000:ℤ)) (.leaf (4578389000000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2224977135176701:ℤ)) (.leaf (2810324374264848:ℤ))), (.branch 124 (.leaf (2246114593932657:ℤ)) (.leaf (2852114427298328:ℤ))), (.branch 124 (.leaf (2252720368692461:ℤ)) (.leaf (2881996185234453:ℤ))), (.branch 124 (.leaf (2275128066088630:ℤ)) (.leaf (2927483813279517:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 40 28) 8000 (endpointMeanRuns 40 28) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 40 28, EndpointRunConditions (endpointMeanCutoff 40 28) (endpointMeanBox 40 28).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 28, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 40 28 h) (endpointMeanCornerA 40 28 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 28, endpointJoint24Q (endpointMeanCornerK 40 28 h) (endpointMeanCornerA 40 28 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 40 28, endpointRunWeightQ (endpointMeanCutoff 40 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 40 28) = (185896091/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 40 28 h = (logRoundedQ ((endpointMeanCutoff 40 28:ℚ)/200)).2+(185896091/500000000000000:ℚ)+((endpointMeanRuns 40 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 40 28).map (fun r => endpointRunWeightQ (endpointMeanCutoff 40 28) r*endpointJoint24Q (endpointMeanCornerK 40 28 h) (endpointMeanCornerA 40 28 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 40 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 40 28 h≤endpointMeanCorner 40 28 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 40 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint40_28

namespace EndpointAnalyticJoint40_29
private noncomputable def weights : IntegerLookupTree := (.leaf (212231193600000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2246114593932657:ℤ)), (.leaf (2258893335112714:ℤ)), (.leaf (2275128066088630:ℤ)), (.leaf (2288679529486633:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 40 29) 8000 (endpointMeanRuns 40 29) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 40 29, EndpointRunConditions (endpointMeanCutoff 40 29) (endpointMeanBox 40 29).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 29, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 40 29 h) (endpointMeanCornerA 40 29 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 29, endpointJoint24Q (endpointMeanCornerK 40 29 h) (endpointMeanCornerA 40 29 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 40 29, endpointRunWeightQ (endpointMeanCutoff 40 29) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 40 29) = (23181697/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 40 29 h = (logRoundedQ ((endpointMeanCutoff 40 29:ℚ)/200)).2+(23181697/62500000000000:ℚ)+((endpointMeanRuns 40 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 40 29).map (fun r => endpointRunWeightQ (endpointMeanCutoff 40 29) r*endpointJoint24Q (endpointMeanCornerK 40 29 h) (endpointMeanCornerA 40 29 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 40 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 40 29 h≤endpointMeanCorner 40 29 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 40 29 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint40_29

namespace EndpointAnalyticJoint40_30
private noncomputable def weights : IntegerLookupTree := (.branch 2536 (.leaf (118003366400000:ℤ)) (.leaf (4552814600000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2258893335112714:ℤ)) (.leaf (2877486155231051:ℤ))), (.branch 124 (.leaf (2267452860218539:ℤ)) (.leaf (2894525906295481:ℤ))), (.branch 124 (.leaf (2288679529486633:ℤ)) (.leaf (2955120284048509:ℤ))), (.branch 124 (.leaf (2297758651735626:ℤ)) (.leaf (2973689389639632:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 40 30) 8000 (endpointMeanRuns 40 30) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 40 30, EndpointRunConditions (endpointMeanCutoff 40 30) (endpointMeanBox 40 30).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 30, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 40 30 h) (endpointMeanCornerA 40 30 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 30, endpointJoint24Q (endpointMeanCornerK 40 30 h) (endpointMeanCornerA 40 30 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 40 30, endpointRunWeightQ (endpointMeanCutoff 40 30) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 40 30) = (185202229/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 40 30 h = (logRoundedQ ((endpointMeanCutoff 40 30:ℚ)/200)).2+(185202229/500000000000000:ℚ)+((endpointMeanRuns 40 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 40 30).map (fun r => endpointRunWeightQ (endpointMeanCutoff 40 30) r*endpointJoint24Q (endpointMeanCornerK 40 30 h) (endpointMeanCornerA 40 30 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 40 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 40 30 h≤endpointMeanCorner 40 30 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 40 30 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint40_30

namespace EndpointAnalyticJoint40_31
private noncomputable def weights : IntegerLookupTree := (.branch 2536 (.leaf (115292307700000:ℤ)) (.leaf (4536699000000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2267452860218539:ℤ)) (.leaf (2894525906295481:ℤ))), (.branch 124 (.leaf (2288993841721760:ℤ)) (.leaf (2937568051977516:ℤ))), (.branch 124 (.leaf (2297758651735626:ℤ)) (.leaf (2973689389639632:ℤ))), (.branch 124 (.leaf (2320614342691796:ℤ)) (.leaf (3020624245962653:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 40 31) 8000 (endpointMeanRuns 40 31) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 40 31, EndpointRunConditions (endpointMeanCutoff 40 31) (endpointMeanBox 40 31).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 31, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 40 31 h) (endpointMeanCornerA 40 31 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 40 31, endpointJoint24Q (endpointMeanCornerK 40 31 h) (endpointMeanCornerA 40 31 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 40 31, endpointRunWeightQ (endpointMeanCutoff 40 31) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 40 31) = (369529993/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 40 31 h = (logRoundedQ ((endpointMeanCutoff 40 31:ℚ)/200)).2+(369529993/1000000000000000:ℚ)+((endpointMeanRuns 40 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 40 31).map (fun r => endpointRunWeightQ (endpointMeanCutoff 40 31) r*endpointJoint24Q (endpointMeanCornerK 40 31 h) (endpointMeanCornerA 40 31 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 40 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 40 31 h≤endpointMeanCorner 40 31 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 40 31 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint40_31

namespace EndpointAnalyticJoint41_17
private noncomputable def weights : IntegerLookupTree := (.branch 1664 (.leaf (100882998600000:ℤ)) (.branch 2495 (.leaf (15715222000000:ℤ)) (.leaf (5276504800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2035042478514117:ℤ)) (.branch 136 (.leaf (2453950260379680:ℤ)) (.leaf (2905678532673545:ℤ)))), (.branch 124 (.leaf (2040429835084342:ℤ)) (.branch 136 (.leaf (2464236542315284:ℤ)) (.leaf (2922651569432867:ℤ)))), (.branch 124 (.leaf (2052405830716180:ℤ)) (.branch 136 (.leaf (2498369071690953:ℤ)) (.leaf (3002174442100552:ℤ)))), (.branch 124 (.leaf (2058102521018594:ℤ)) (.branch 136 (.leaf (2509519563356731:ℤ)) (.leaf (3021197523127529:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 41 17) 8000 (endpointMeanRuns 41 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 41 17, EndpointRunConditions (endpointMeanCutoff 41 17) (endpointMeanBox 41 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 41 17 h) (endpointMeanCornerA 41 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 17, endpointJoint24Q (endpointMeanCornerK 41 17 h) (endpointMeanCornerA 41 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 41 17, endpointRunWeightQ (endpointMeanCutoff 41 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 41 17) = (19079481/50000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 41 17 h = (logRoundedQ ((endpointMeanCutoff 41 17:ℚ)/200)).2+(19079481/50000000000000:ℚ)+((endpointMeanRuns 41 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 41 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 41 17) r*endpointJoint24Q (endpointMeanCornerK 41 17 h) (endpointMeanCornerA 41 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 41 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 41 17 h≤endpointMeanCorner 41 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 41 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint41_17

namespace EndpointAnalyticJoint41_18
private noncomputable def weights : IntegerLookupTree := (.branch 1664 (.leaf (98555661800000:ℤ)) (.branch 2495 (.leaf (15653523300000:ℤ)) (.leaf (5259513800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2040429835084342:ℤ)) (.branch 136 (.leaf (2464236542315284:ℤ)) (.leaf (2922651569432867:ℤ)))), (.branch 124 (.leaf (2060725889107777:ℤ)) (.branch 136 (.leaf (2503130513038143:ℤ)) (.leaf (2987080075400051:ℤ)))), (.branch 124 (.leaf (2058102521018594:ℤ)) (.branch 136 (.leaf (2509519563356731:ℤ)) (.leaf (3021197523127529:ℤ)))), (.branch 124 (.leaf (2079570466758822:ℤ)) (.branch 136 (.leaf (2551708324705765:ℤ)) (.leaf (3093492427997107:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 41 18) 8000 (endpointMeanRuns 41 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 41 18, EndpointRunConditions (endpointMeanCutoff 41 18) (endpointMeanBox 41 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 41 18 h) (endpointMeanCornerA 41 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 18, endpointJoint24Q (endpointMeanCornerK 41 18 h) (endpointMeanCornerA 41 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 41 18, endpointRunWeightQ (endpointMeanCutoff 41 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 41 18) = (19038171/50000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 41 18 h = (logRoundedQ ((endpointMeanCutoff 41 18:ℚ)/200)).2+(19038171/50000000000000:ℚ)+((endpointMeanRuns 41 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 41 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 41 18) r*endpointJoint24Q (endpointMeanCornerK 41 18 h) (endpointMeanCornerA 41 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 41 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 41 18 h≤endpointMeanCorner 41 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 41 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint41_18

namespace EndpointAnalyticJoint41_19
private noncomputable def weights : IntegerLookupTree := (.branch 1331 (.leaf (62094922300000:ℤ)) (.branch 2495 (.leaf (41579605600000:ℤ)) (.leaf (5234253800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2060725889107777:ℤ)) (.branch 145 (.leaf (2503130513038143:ℤ)) (.leaf (3544506011282879:ℤ)))), (.branch 124 (.leaf (2081223826970509:ℤ)) (.branch 145 (.leaf (2542638361906464:ℤ)) (.leaf (3646766353880002:ℤ)))), (.branch 124 (.leaf (2079570466758822:ℤ)) (.branch 145 (.leaf (2551708324705765:ℤ)) (.leaf (3762856523091205:ℤ)))), (.branch 124 (.leaf (2101262343372070:ℤ)) (.branch 145 (.leaf (2594606341965833:ℤ)) (.leaf (3883616155668316:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 41 19) 8000 (endpointMeanRuns 41 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 41 19, EndpointRunConditions (endpointMeanCutoff 41 19) (endpointMeanBox 41 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 41 19 h) (endpointMeanCornerA 41 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 19, endpointJoint24Q (endpointMeanCornerK 41 19 h) (endpointMeanCornerA 41 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 41 19, endpointRunWeightQ (endpointMeanCutoff 41 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 41 19) = (189767567/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 41 19 h = (logRoundedQ ((endpointMeanCutoff 41 19:ℚ)/200)).2+(189767567/500000000000000:ℚ)+((endpointMeanRuns 41 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 41 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 41 19) r*endpointJoint24Q (endpointMeanCornerK 41 19 h) (endpointMeanCornerA 41 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 41 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 41 19 h≤endpointMeanCorner 41 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 41 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint41_19

namespace EndpointAnalyticJoint41_20
private noncomputable def weights : IntegerLookupTree := (.branch 1815 (.leaf (103974875000000:ℤ)) (.branch 2495 (.leaf (9545585200000:ℤ)) (.leaf (5209260500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2081223826970509:ℤ)) (.branch 133 (.leaf (2542638361906464:ℤ)) (.leaf (2903147824222388:ℤ)))), (.branch 124 (.leaf (2101925656801037:ℤ)) (.branch 133 (.leaf (2582769777989552:ℤ)) (.leaf (2961913123859377:ℤ)))), (.branch 124 (.leaf (2101262343372070:ℤ)) (.branch 133 (.leaf (2594606341965833:ℤ)) (.leaf (2995847431310285:ℤ)))), (.branch 124 (.leaf (2123180486668043:ℤ)) (.branch 133 (.leaf (2638225538785114:ℤ)) (.leaf (3061296433259873:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 41 20) 8000 (endpointMeanRuns 41 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 41 20, EndpointRunConditions (endpointMeanCutoff 41 20) (endpointMeanBox 41 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 41 20 h) (endpointMeanCornerA 41 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 20, endpointJoint24Q (endpointMeanCornerK 41 20 h) (endpointMeanCornerA 41 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 41 20, endpointRunWeightQ (endpointMeanCutoff 41 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 41 20) = (47289977/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 41 20 h = (logRoundedQ ((endpointMeanCutoff 41 20:ℚ)/200)).2+(47289977/125000000000000:ℚ)+((endpointMeanRuns 41 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 41 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 41 20) r*endpointJoint24Q (endpointMeanCornerK 41 20 h) (endpointMeanCornerA 41 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 41 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 41 20 h≤endpointMeanCorner 41 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 41 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint41_20

namespace EndpointAnalyticJoint41_21
private noncomputable def weights : IntegerLookupTree := (.branch 1361 (.leaf (60221922800000:ℤ)) (.branch 2495 (.leaf (37704973200000:ℤ)) (.leaf (5184528200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2101925656801037:ℤ)) (.branch 144 (.leaf (2582769777989552:ℤ)) (.leaf (3666321973139579:ℤ)))), (.branch 124 (.leaf (2122833406702626:ℤ)) (.branch 144 (.leaf (2623534603282914:ℤ)) (.leaf (3768848057174032:ℤ)))), (.branch 124 (.leaf (2123180486668043:ℤ)) (.branch 144 (.leaf (2638225538785114:ℤ)) (.leaf (3900468703276359:ℤ)))), (.branch 124 (.leaf (2145327256821133:ℤ)) (.branch 144 (.leaf (2682578039266063:ℤ)) (.leaf (4021380058199131:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 41 21) 8000 (endpointMeanRuns 41 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 41 21, EndpointRunConditions (endpointMeanCutoff 41 21) (endpointMeanBox 41 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 41 21 h) (endpointMeanCornerA 41 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 21, endpointJoint24Q (endpointMeanCornerK 41 21 h) (endpointMeanCornerA 41 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 41 21, endpointRunWeightQ (endpointMeanCutoff 41 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 41 21) = (188558597/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 41 21 h = (logRoundedQ ((endpointMeanCutoff 41 21:ℚ)/200)).2+(188558597/500000000000000:ℚ)+((endpointMeanRuns 41 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 41 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 41 21) r*endpointJoint24Q (endpointMeanCornerK 41 21 h) (endpointMeanCornerA 41 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 41 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 41 21 h≤endpointMeanCorner 41 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 41 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint41_21

namespace EndpointAnalyticJoint41_22
private noncomputable def weights : IntegerLookupTree := (.branch 1393 (.leaf (60998632100000:ℤ)) (.branch 2495 (.leaf (34201090300000:ℤ)) (.leaf (5160051700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2122833406702626:ℤ)) (.branch 143 (.leaf (2623534603282914:ℤ)) (.leaf (3682551217480882:ℤ)))), (.branch 124 (.leaf (2143949124951966:ℤ)) (.branch 143 (.leaf (2664942835121986:ℤ)) (.leaf (3782407023493337:ℤ)))), (.branch 124 (.leaf (2145327256821133:ℤ)) (.branch 143 (.leaf (2682578039266063:ℤ)) (.leaf (3913670687349946:ℤ)))), (.branch 124 (.leaf (2167705038624572:ℤ)) (.branch 143 (.leaf (2727676171335361:ℤ)) (.leaf (4030930942319684:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 41 22) 8000 (endpointMeanRuns 41 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 41 22, EndpointRunConditions (endpointMeanCutoff 41 22) (endpointMeanBox 41 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 41 22 h) (endpointMeanCornerA 41 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 22, endpointJoint24Q (endpointMeanCornerK 41 22 h) (endpointMeanCornerA 41 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 41 22, endpointRunWeightQ (endpointMeanCutoff 41 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 41 22) = (187963503/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 41 22 h = (logRoundedQ ((endpointMeanCutoff 41 22:ℚ)/200)).2+(187963503/500000000000000:ℚ)+((endpointMeanRuns 41 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 41 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 41 22) r*endpointJoint24Q (endpointMeanCornerK 41 22 h) (endpointMeanCornerA 41 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 41 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 41 22 h≤endpointMeanCorner 41 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 41 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint41_22

namespace EndpointAnalyticJoint41_23
private noncomputable def weights : IntegerLookupTree := (.branch 2495 (.leaf (132395266800000:ℤ)) (.leaf (5138505200000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2143949124951966:ℤ)) (.leaf (2664942835121986:ℤ))), (.branch 124 (.leaf (2165274880199868:ℤ)) (.leaf (2707004628633872:ℤ))), (.branch 124 (.leaf (2167705038624572:ℤ)) (.leaf (2727676171335361:ℤ))), (.branch 124 (.leaf (2190316241747226:ℤ)) (.leaf (2773532470170501:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 41 23) 8000 (endpointMeanRuns 41 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 41 23, EndpointRunConditions (endpointMeanCutoff 41 23) (endpointMeanBox 41 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 41 23 h) (endpointMeanCornerA 41 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 23, endpointJoint24Q (endpointMeanCornerK 41 23 h) (endpointMeanCornerA 41 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 41 23, endpointRunWeightQ (endpointMeanCutoff 41 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 41 23) = (374879293/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 41 23 h = (logRoundedQ ((endpointMeanCutoff 41 23:ℚ)/200)).2+(374879293/1000000000000000:ℚ)+((endpointMeanRuns 41 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 41 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 41 23) r*endpointJoint24Q (endpointMeanCornerK 41 23 h) (endpointMeanCornerA 41 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 41 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 41 23 h≤endpointMeanCorner 41 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 41 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint41_23

namespace EndpointAnalyticJoint41_24
private noncomputable def weights : IntegerLookupTree := (.branch 2495 (.leaf (128483820400000:ℤ)) (.leaf (5114497500000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2165274880199868:ℤ)) (.leaf (2707004628633872:ℤ))), (.branch 124 (.leaf (2186812761673896:ℤ)) (.leaf (2749730299227900:ℤ))), (.branch 124 (.leaf (2190316241747226:ℤ)) (.leaf (2773532470170501:ℤ))), (.branch 124 (.leaf (2213163300993089:ℤ)) (.leaf (2820159681683969:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 41 24) 8000 (endpointMeanRuns 41 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 41 24, EndpointRunConditions (endpointMeanCutoff 41 24) (endpointMeanBox 41 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 41 24 h) (endpointMeanCornerA 41 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 24, endpointJoint24Q (endpointMeanCornerK 41 24 h) (endpointMeanCornerA 41 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 41 24, endpointRunWeightQ (endpointMeanCutoff 41 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 41 24) = (373711903/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 41 24 h = (logRoundedQ ((endpointMeanCutoff 41 24:ℚ)/200)).2+(373711903/1000000000000000:ℚ)+((endpointMeanRuns 41 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 41 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 41 24) r*endpointJoint24Q (endpointMeanCornerK 41 24 h) (endpointMeanCornerA 41 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 41 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 41 24 h≤endpointMeanCorner 41 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 41 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint41_24

namespace EndpointAnalyticJoint41_25
private noncomputable def weights : IntegerLookupTree := (.branch 2495 (.leaf (124690363900000:ℤ)) (.leaf (5090730900000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2186812761673896:ℤ)) (.leaf (2749730299227900:ℤ))), (.branch 124 (.leaf (2208564879383070:ℤ)) (.leaf (2793130325125347:ℤ))), (.branch 124 (.leaf (2213163300993089:ℤ)) (.leaf (2820159681683969:ℤ))), (.branch 124 (.leaf (2236248676563426:ℤ)) (.leaf (2867570766066029:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 41 25) 8000 (endpointMeanRuns 41 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 41 25, EndpointRunConditions (endpointMeanCutoff 41 25) (endpointMeanBox 41 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 41 25 h) (endpointMeanCornerA 41 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 25, endpointJoint24Q (endpointMeanCornerK 41 25 h) (endpointMeanCornerA 41 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 41 25, endpointRunWeightQ (endpointMeanCutoff 41 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 41 25) = (372556233/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 41 25 h = (logRoundedQ ((endpointMeanCutoff 41 25:ℚ)/200)).2+(372556233/1000000000000000:ℚ)+((endpointMeanRuns 41 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 41 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 41 25) r*endpointJoint24Q (endpointMeanCornerK 41 25 h) (endpointMeanCornerA 41 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 41 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 41 25 h≤endpointMeanCorner 41 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 41 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint41_25

namespace EndpointAnalyticJoint41_26
private noncomputable def weights : IntegerLookupTree := (.branch 2495 (.leaf (121011168700000:ℤ)) (.leaf (5067200500000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2208564879383070:ℤ)) (.leaf (2793130325125347:ℤ))), (.branch 124 (.leaf (2230533364324565:ℤ)) (.leaf (2837215349929210:ℤ))), (.branch 124 (.leaf (2236248676563426:ℤ)) (.leaf (2867570766066029:ℤ))), (.branch 124 (.leaf (2259574854321739:ℤ)) (.leaf (2915778901387038:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 41 26) 8000 (endpointMeanRuns 41 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 41 26, EndpointRunConditions (endpointMeanCutoff 41 26) (endpointMeanBox 41 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 41 26 h) (endpointMeanCornerA 41 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 26, endpointJoint24Q (endpointMeanCornerK 41 26 h) (endpointMeanCornerA 41 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 41 26, endpointRunWeightQ (endpointMeanCutoff 41 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 41 26) = (7428241/20000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 41 26 h = (logRoundedQ ((endpointMeanCutoff 41 26:ℚ)/200)).2+(7428241/20000000000000:ℚ)+((endpointMeanRuns 41 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 41 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 41 26) r*endpointJoint24Q (endpointMeanCornerK 41 26 h) (endpointMeanCornerA 41 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 41 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 41 26 h≤endpointMeanCorner 41 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 41 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint41_26

namespace EndpointAnalyticJoint41_27
private noncomputable def weights : IntegerLookupTree := (.branch 2495 (.leaf (117442633600000:ℤ)) (.leaf (5043901600000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2230533364324565:ℤ)) (.leaf (2837215349929210:ℤ))), (.branch 124 (.leaf (2252720368692461:ℤ)) (.leaf (2881996185234453:ℤ))), (.branch 124 (.leaf (2259574854321739:ℤ)) (.leaf (2915778901387038:ℤ))), (.branch 124 (.leaf (2283144346061416:ℤ)) (.leaf (2964797487260351:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 41 27) 8000 (endpointMeanRuns 41 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 41 27, EndpointRunConditions (endpointMeanCutoff 41 27) (endpointMeanBox 41 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 41 27 h) (endpointMeanCornerA 41 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 27, endpointJoint24Q (endpointMeanCornerK 41 27 h) (endpointMeanCornerA 41 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 41 27, endpointRunWeightQ (endpointMeanCutoff 41 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 41 27) = (370279127/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 41 27 h = (logRoundedQ ((endpointMeanCutoff 41 27:ℚ)/200)).2+(370279127/1000000000000000:ℚ)+((endpointMeanRuns 41 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 41 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 41 27) r*endpointJoint24Q (endpointMeanCornerK 41 27 h) (endpointMeanCornerA 41 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 41 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 41 27 h≤endpointMeanCorner 41 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 41 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint41_27

namespace EndpointAnalyticJoint41_28
private noncomputable def weights : IntegerLookupTree := (.branch 2495 (.leaf (113981279400000:ℤ)) (.leaf (5020829800000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2252720368692461:ℤ)) (.leaf (2881996185234453:ℤ))), (.branch 124 (.leaf (2275128066088630:ℤ)) (.leaf (2927483813279517:ℤ))), (.branch 124 (.leaf (2283144346061416:ℤ)) (.leaf (2964797487260351:ℤ))), (.branch 124 (.leaf (2306959689776218:ℤ)) (.leaf (3014640148566780:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 41 28) 8000 (endpointMeanRuns 41 28) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 41 28, EndpointRunConditions (endpointMeanCutoff 41 28) (endpointMeanBox 41 28).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 28, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 41 28 h) (endpointMeanCornerA 41 28 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 28, endpointJoint24Q (endpointMeanCornerK 41 28 h) (endpointMeanCornerA 41 28 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 41 28, endpointRunWeightQ (endpointMeanCutoff 41 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 41 28) = (184578623/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 41 28 h = (logRoundedQ ((endpointMeanCutoff 41 28:ℚ)/200)).2+(184578623/500000000000000:ℚ)+((endpointMeanRuns 41 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 41 28).map (fun r => endpointRunWeightQ (endpointMeanCutoff 41 28) r*endpointJoint24Q (endpointMeanCornerK 41 28 h) (endpointMeanCornerA 41 28 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 41 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 41 28 h≤endpointMeanCorner 41 28 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 41 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint41_28

namespace EndpointAnalyticJoint41_29
private noncomputable def weights : IntegerLookupTree := (.leaf (199789007100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2275128066088630:ℤ)), (.leaf (2288679529486633:ℤ)), (.leaf (2306959689776218:ℤ)), (.leaf (2321367970662042:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 41 29) 8000 (endpointMeanRuns 41 29) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 41 29, EndpointRunConditions (endpointMeanCutoff 41 29) (endpointMeanBox 41 29).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 29, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 41 29 h) (endpointMeanCornerA 41 29 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 29, endpointJoint24Q (endpointMeanCornerK 41 29 h) (endpointMeanCornerA 41 29 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 41 29, endpointRunWeightQ (endpointMeanCutoff 41 29) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 41 29) = (46036521/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 41 29 h = (logRoundedQ ((endpointMeanCutoff 41 29:ℚ)/200)).2+(46036521/125000000000000:ℚ)+((endpointMeanRuns 41 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 41 29).map (fun r => endpointRunWeightQ (endpointMeanCutoff 41 29) r*endpointJoint24Q (endpointMeanCornerK 41 29 h) (endpointMeanCornerA 41 29 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 41 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 41 29 h≤endpointMeanCorner 41 29 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 41 29 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint41_29

namespace EndpointAnalyticJoint41_30
private noncomputable def weights : IntegerLookupTree := (.branch 2495 (.leaf (109527073100000:ℤ)) (.leaf (4990413100000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2288679529486633:ℤ)) (.leaf (2955120284048509:ℤ))), (.branch 124 (.leaf (2297758651735626:ℤ)) (.leaf (2973689389639632:ℤ))), (.branch 124 (.leaf (2321367970662042:ℤ)) (.leaf (3044947055152078:ℤ))), (.branch 124 (.leaf (2331023449933551:ℤ)) (.leaf (3065320739241667:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 41 30) 8000 (endpointMeanRuns 41 30) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 41 30, EndpointRunConditions (endpointMeanCutoff 41 30) (endpointMeanBox 41 30).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 30, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 41 30 h) (endpointMeanCornerA 41 30 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 30, endpointJoint24Q (endpointMeanCornerK 41 30 h) (endpointMeanCornerA 41 30 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 41 30, endpointRunWeightQ (endpointMeanCutoff 41 30) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 41 30) = (367678211/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 41 30 h = (logRoundedQ ((endpointMeanCutoff 41 30:ℚ)/200)).2+(367678211/1000000000000000:ℚ)+((endpointMeanRuns 41 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 41 30).map (fun r => endpointRunWeightQ (endpointMeanCutoff 41 30) r*endpointJoint24Q (endpointMeanCornerK 41 30 h) (endpointMeanCornerA 41 30 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 41 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 41 30 h≤endpointMeanCorner 41 30 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 41 30 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint41_30

namespace EndpointAnalyticJoint41_31
private noncomputable def weights : IntegerLookupTree := (.branch 2495 (.leaf (107366781700000:ℤ)) (.leaf (4975350000000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2297758651735626:ℤ)) (.leaf (2973689389639632:ℤ))), (.branch 124 (.leaf (2320614342691796:ℤ)) (.leaf (3020624245962653:ℤ))), (.branch 124 (.leaf (2331023449933551:ℤ)) (.leaf (3065320739241667:ℤ))), (.branch 124 (.leaf (2355338217750656:ℤ)) (.leaf (3116853346125643:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 41 31) 8000 (endpointMeanRuns 41 31) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 41 31, EndpointRunConditions (endpointMeanCutoff 41 31) (endpointMeanBox 41 31).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 31, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 41 31 h) (endpointMeanCornerA 41 31 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 31, endpointJoint24Q (endpointMeanCornerK 41 31 h) (endpointMeanCornerA 41 31 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 41 31, endpointRunWeightQ (endpointMeanCutoff 41 31) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 41 31) = (366945759/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 41 31 h = (logRoundedQ ((endpointMeanCutoff 41 31:ℚ)/200)).2+(366945759/1000000000000000:ℚ)+((endpointMeanRuns 41 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 41 31).map (fun r => endpointRunWeightQ (endpointMeanCutoff 41 31) r*endpointJoint24Q (endpointMeanCornerK 41 31 h) (endpointMeanCornerA 41 31 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 41 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 41 31 h≤endpointMeanCorner 41 31 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 41 31 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint41_31

namespace EndpointAnalyticJoint41_32
private noncomputable def weights : IntegerLookupTree := (.branch 2495 (.leaf (104207250400000:ℤ)) (.leaf (4952933700000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 124 (.leaf (2320614342691796:ℤ)) (.leaf (3020624245962653:ℤ))), (.branch 124 (.leaf (2343697378068448:ℤ)) (.leaf (3068299892748107:ℤ))), (.branch 124 (.leaf (2355338217750656:ℤ)) (.leaf (3116853346125643:ℤ))), (.branch 124 (.leaf (2379906611473592:ℤ)) (.leaf (3169252292880114:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 41 32) 8000 (endpointMeanRuns 41 32) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 41 32, EndpointRunConditions (endpointMeanCutoff 41 32) (endpointMeanBox 41 32).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 32, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 41 32 h) (endpointMeanCornerA 41 32 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 41 32, endpointJoint24Q (endpointMeanCornerK 41 32 h) (endpointMeanCornerA 41 32 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 41 32, endpointRunWeightQ (endpointMeanCutoff 41 32) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 41 32) = (365855747/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 41 32 h = (logRoundedQ ((endpointMeanCutoff 41 32:ℚ)/200)).2+(365855747/1000000000000000:ℚ)+((endpointMeanRuns 41 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 41 32).map (fun r => endpointRunWeightQ (endpointMeanCutoff 41 32) r*endpointJoint24Q (endpointMeanCornerK 41 32 h) (endpointMeanCornerA 41 32 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 41 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 41 32 h≤endpointMeanCorner 41 32 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 41 32 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint41_32

private theorem activeIndices36 : ∀ai : Fin 42, endpointMeanActive 36 ai → ai∈
    ([13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow36 (ai : Fin 42) : endpointMeanActive 36 ai →
    EndpointJointNumericalConditions 36 ai := by
  intro hact
  have hi := activeIndices36 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint36_13.conditions
  · exact EndpointAnalyticJoint36_14.conditions
  · exact EndpointAnalyticJoint36_15.conditions
  · exact EndpointAnalyticJoint36_16.conditions
  · exact EndpointAnalyticJoint36_17.conditions
  · exact EndpointAnalyticJoint36_18.conditions
  · exact EndpointAnalyticJoint36_19.conditions
  · exact EndpointAnalyticJoint36_20.conditions
  · exact EndpointAnalyticJoint36_21.conditions
  · exact EndpointAnalyticJoint36_22.conditions
  · exact EndpointAnalyticJoint36_23.conditions
  · exact EndpointAnalyticJoint36_24.conditions
  · exact EndpointAnalyticJoint36_25.conditions
  · exact EndpointAnalyticJoint36_26.conditions
  · exact EndpointAnalyticJoint36_27.conditions
  · exact EndpointAnalyticJoint36_28.conditions

private theorem activeIndices37 : ∀ai : Fin 42, endpointMeanActive 37 ai → ai∈
    ([14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow37 (ai : Fin 42) : endpointMeanActive 37 ai →
    EndpointJointNumericalConditions 37 ai := by
  intro hact
  have hi := activeIndices37 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint37_14.conditions
  · exact EndpointAnalyticJoint37_15.conditions
  · exact EndpointAnalyticJoint37_16.conditions
  · exact EndpointAnalyticJoint37_17.conditions
  · exact EndpointAnalyticJoint37_18.conditions
  · exact EndpointAnalyticJoint37_19.conditions
  · exact EndpointAnalyticJoint37_20.conditions
  · exact EndpointAnalyticJoint37_21.conditions
  · exact EndpointAnalyticJoint37_22.conditions
  · exact EndpointAnalyticJoint37_23.conditions
  · exact EndpointAnalyticJoint37_24.conditions
  · exact EndpointAnalyticJoint37_25.conditions
  · exact EndpointAnalyticJoint37_26.conditions
  · exact EndpointAnalyticJoint37_27.conditions
  · exact EndpointAnalyticJoint37_28.conditions
  · exact EndpointAnalyticJoint37_29.conditions

private theorem activeIndices38 : ∀ai : Fin 42, endpointMeanActive 38 ai → ai∈
    ([15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow38 (ai : Fin 42) : endpointMeanActive 38 ai →
    EndpointJointNumericalConditions 38 ai := by
  intro hact
  have hi := activeIndices38 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint38_15.conditions
  · exact EndpointAnalyticJoint38_16.conditions
  · exact EndpointAnalyticJoint38_17.conditions
  · exact EndpointAnalyticJoint38_18.conditions
  · exact EndpointAnalyticJoint38_19.conditions
  · exact EndpointAnalyticJoint38_20.conditions
  · exact EndpointAnalyticJoint38_21.conditions
  · exact EndpointAnalyticJoint38_22.conditions
  · exact EndpointAnalyticJoint38_23.conditions
  · exact EndpointAnalyticJoint38_24.conditions
  · exact EndpointAnalyticJoint38_25.conditions
  · exact EndpointAnalyticJoint38_26.conditions
  · exact EndpointAnalyticJoint38_27.conditions
  · exact EndpointAnalyticJoint38_28.conditions
  · exact EndpointAnalyticJoint38_29.conditions

private theorem activeIndices39 : ∀ai : Fin 42, endpointMeanActive 39 ai → ai∈
    ([16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow39 (ai : Fin 42) : endpointMeanActive 39 ai →
    EndpointJointNumericalConditions 39 ai := by
  intro hact
  have hi := activeIndices39 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint39_16.conditions
  · exact EndpointAnalyticJoint39_17.conditions
  · exact EndpointAnalyticJoint39_18.conditions
  · exact EndpointAnalyticJoint39_19.conditions
  · exact EndpointAnalyticJoint39_20.conditions
  · exact EndpointAnalyticJoint39_21.conditions
  · exact EndpointAnalyticJoint39_22.conditions
  · exact EndpointAnalyticJoint39_23.conditions
  · exact EndpointAnalyticJoint39_24.conditions
  · exact EndpointAnalyticJoint39_25.conditions
  · exact EndpointAnalyticJoint39_26.conditions
  · exact EndpointAnalyticJoint39_27.conditions
  · exact EndpointAnalyticJoint39_28.conditions
  · exact EndpointAnalyticJoint39_29.conditions
  · exact EndpointAnalyticJoint39_30.conditions
  · exact EndpointAnalyticJoint39_31.conditions

private theorem activeIndices40 : ∀ai : Fin 42, endpointMeanActive 40 ai → ai∈
    ([16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow40 (ai : Fin 42) : endpointMeanActive 40 ai →
    EndpointJointNumericalConditions 40 ai := by
  intro hact
  have hi := activeIndices40 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint40_16.conditions
  · exact EndpointAnalyticJoint40_17.conditions
  · exact EndpointAnalyticJoint40_18.conditions
  · exact EndpointAnalyticJoint40_19.conditions
  · exact EndpointAnalyticJoint40_20.conditions
  · exact EndpointAnalyticJoint40_21.conditions
  · exact EndpointAnalyticJoint40_22.conditions
  · exact EndpointAnalyticJoint40_23.conditions
  · exact EndpointAnalyticJoint40_24.conditions
  · exact EndpointAnalyticJoint40_25.conditions
  · exact EndpointAnalyticJoint40_26.conditions
  · exact EndpointAnalyticJoint40_27.conditions
  · exact EndpointAnalyticJoint40_28.conditions
  · exact EndpointAnalyticJoint40_29.conditions
  · exact EndpointAnalyticJoint40_30.conditions
  · exact EndpointAnalyticJoint40_31.conditions

private theorem activeIndices41 : ∀ai : Fin 42, endpointMeanActive 41 ai → ai∈
    ([17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow41 (ai : Fin 42) : endpointMeanActive 41 ai →
    EndpointJointNumericalConditions 41 ai := by
  intro hact
  have hi := activeIndices41 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint41_17.conditions
  · exact EndpointAnalyticJoint41_18.conditions
  · exact EndpointAnalyticJoint41_19.conditions
  · exact EndpointAnalyticJoint41_20.conditions
  · exact EndpointAnalyticJoint41_21.conditions
  · exact EndpointAnalyticJoint41_22.conditions
  · exact EndpointAnalyticJoint41_23.conditions
  · exact EndpointAnalyticJoint41_24.conditions
  · exact EndpointAnalyticJoint41_25.conditions
  · exact EndpointAnalyticJoint41_26.conditions
  · exact EndpointAnalyticJoint41_27.conditions
  · exact EndpointAnalyticJoint41_28.conditions
  · exact EndpointAnalyticJoint41_29.conditions
  · exact EndpointAnalyticJoint41_30.conditions
  · exact EndpointAnalyticJoint41_31.conditions
  · exact EndpointAnalyticJoint41_32.conditions

end SingularValueBounds.KL.Certificates
