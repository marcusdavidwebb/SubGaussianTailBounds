import SingularValueBounds.KL.Certificates.EndpointAnalyticLogs
import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SingularValueBounds.KL.Certificates

namespace EndpointAnalyticJoint18_04
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 952 (.leaf (126617271300000:ℤ)) (.leaf (42184141100000:ℤ))) (.branch 2116 (.leaf (13142601200000:ℤ)) (.leaf (13768426800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 145 (.leaf (1775203531719341:ℤ)) (.leaf (2137299140040909:ℤ))) (.branch 200 (.leaf (2377441885158326:ℤ)) (.leaf (2928326669407245:ℤ)))), (.branch 164 (.branch 145 (.leaf (1780798075374538:ℤ)) (.leaf (2149615941147921:ℤ))) (.branch 200 (.leaf (2395714168849219:ℤ)) (.leaf (2964809670659031:ℤ)))), (.branch 164 (.branch 145 (.leaf (1776482266623009:ℤ)) (.leaf (2140490070303395:ℤ))) (.branch 200 (.leaf (2382538937274388:ℤ)) (.leaf (2940151824385469:ℤ)))), (.branch 164 (.branch 145 (.leaf (1782294318756147:ℤ)) (.leaf (2153359597400559:ℤ))) (.branch 200 (.leaf (2401705878239794:ℤ)) (.leaf (2978778467575754:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 18 4) 8000 (endpointMeanRuns 18 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 18 4, EndpointRunConditions (endpointMeanCutoff 18 4) (endpointMeanBox 18 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 18 4 h) (endpointMeanCornerA 18 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 4, endpointJoint24Q (endpointMeanCornerK 18 4 h) (endpointMeanCornerA 18 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 18 4, endpointRunWeightQ (endpointMeanCutoff 18 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 18 4) = (453504657/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 18 4 h = (logRoundedQ ((endpointMeanCutoff 18 4:ℚ)/200)).2+(453504657/1000000000000000:ℚ)+((endpointMeanRuns 18 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 18 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 18 4) r*endpointJoint24Q (endpointMeanCornerK 18 4 h) (endpointMeanCornerA 18 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 18 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 18 4 h≤endpointMeanCorner 18 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 18 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint18_04

namespace EndpointAnalyticJoint18_05
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 952 (.leaf (122871975700000:ℤ)) (.leaf (41939286400000:ℤ))) (.branch 2116 (.leaf (13079675300000:ℤ)) (.leaf (13711673600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 145 (.leaf (1780798075374538:ℤ)) (.leaf (2149615941147921:ℤ))) (.branch 200 (.leaf (2395714168849219:ℤ)) (.leaf (2964809670659031:ℤ)))), (.branch 164 (.branch 145 (.leaf (1788672894087781:ℤ)) (.leaf (2167007173727279:ℤ))) (.branch 200 (.leaf (2421573786015131:ℤ)) (.leaf (3016735860739775:ℤ)))), (.branch 164 (.branch 145 (.leaf (1782294318756147:ℤ)) (.leaf (2153359597400559:ℤ))) (.branch 200 (.leaf (2401705878239794:ℤ)) (.leaf (2978778467575754:ℤ)))), (.branch 164 (.branch 145 (.leaf (1790476477434400:ℤ)) (.leaf (2171536694733912:ℤ))) (.branch 200 (.leaf (2428843263972658:ℤ)) (.leaf (3033800025333983:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 18 5) 8000 (endpointMeanRuns 18 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 18 5, EndpointRunConditions (endpointMeanCutoff 18 5) (endpointMeanBox 18 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 18 5 h) (endpointMeanCornerA 18 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 5, endpointJoint24Q (endpointMeanCornerK 18 5 h) (endpointMeanCornerA 18 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 18 5, endpointRunWeightQ (endpointMeanCutoff 18 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 18 5) = (113055323/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 18 5 h = (logRoundedQ ((endpointMeanCutoff 18 5:ℚ)/200)).2+(113055323/250000000000000:ℚ)+((endpointMeanRuns 18 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 18 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 18 5) r*endpointJoint24Q (endpointMeanCornerK 18 5 h) (endpointMeanCornerA 18 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 18 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 18 5 h≤endpointMeanCorner 18 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 18 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint18_05

namespace EndpointAnalyticJoint18_06
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 952 (.leaf (118518093000000:ℤ)) (.leaf (41649019100000:ℤ))) (.branch 2116 (.leaf (13005078800000:ℤ)) (.leaf (13644394500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 145 (.leaf (1788672894087781:ℤ)) (.leaf (2167007173727279:ℤ))) (.branch 200 (.leaf (2421573786015131:ℤ)) (.leaf (3016735860739775:ℤ)))), (.branch 164 (.branch 145 (.leaf (1796582535822578:ℤ)) (.leaf (2184539108171021:ℤ))) (.branch 200 (.leaf (2447712534894113:ℤ)) (.leaf (3069571495107281:ℤ)))), (.branch 164 (.branch 145 (.leaf (1790476477434400:ℤ)) (.leaf (2171536694733912:ℤ))) (.branch 200 (.leaf (2428843263972658:ℤ)) (.leaf (3033800025333983:ℤ)))), (.branch 164 (.branch 145 (.leaf (1798696198775526:ℤ)) (.leaf (2189867229917520:ℤ))) (.branch 200 (.leaf (2456287280800979:ℤ)) (.leaf (3089837896272630:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 18 6) 8000 (endpointMeanRuns 18 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 18 6, EndpointRunConditions (endpointMeanCutoff 18 6) (endpointMeanBox 18 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 18 6 h) (endpointMeanCornerA 18 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 6, endpointJoint24Q (endpointMeanCornerK 18 6 h) (endpointMeanCornerA 18 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 18 6, endpointRunWeightQ (endpointMeanCutoff 18 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 18 6) = (90139981/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 18 6 h = (logRoundedQ ((endpointMeanCutoff 18 6:ℚ)/200)).2+(90139981/200000000000000:ℚ)+((endpointMeanRuns 18 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 18 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 18 6) r*endpointJoint24Q (endpointMeanCornerK 18 6 h) (endpointMeanCornerA 18 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 18 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 18 6 h≤endpointMeanCorner 18 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 18 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint18_06

namespace EndpointAnalyticJoint18_07
private noncomputable def weights : IntegerLookupTree := (.branch 1134 (.branch 952 (.leaf (114312207000000:ℤ)) (.leaf (13955388900000:ℤ))) (.branch 1488 (.leaf (17988089100000:ℤ)) (.branch 2116 (.leaf (12931455200000:ℤ)) (.leaf (13577993000000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 145 (.leaf (1796582535822578:ℤ)) (.leaf (2184539108171021:ℤ))) (.branch 184 (.leaf (2447712534894113:ℤ)) (.branch 200 (.leaf (2770406112054787:ℤ)) (.leaf (3069571495107281:ℤ))))), (.branch 164 (.branch 145 (.leaf (1804527154568871:ℤ)) (.leaf (2202212882812189:ℤ))) (.branch 184 (.leaf (2474133428466309:ℤ)) (.branch 200 (.leaf (2809863509172591:ℤ)) (.leaf (3123332501926293:ℤ))))), (.branch 164 (.branch 145 (.leaf (1798696198775526:ℤ)) (.leaf (2189867229917520:ℤ))) (.branch 184 (.leaf (2456287280800979:ℤ)) (.branch 200 (.leaf (2784297387414616:ℤ)) (.leaf (3089837896272630:ℤ))))), (.branch 164 (.branch 145 (.leaf (1806953655222234:ℤ)) (.leaf (2208352498162256:ℤ))) (.branch 184 (.leaf (2484041393414755:ℤ)) (.branch 200 (.leaf (2825971120784575:ℤ)) (.leaf (3146910852896927:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 18 7) 8000 (endpointMeanRuns 18 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 18 7, EndpointRunConditions (endpointMeanCutoff 18 7) (endpointMeanBox 18 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 18 7 h) (endpointMeanCornerA 18 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 7, endpointJoint24Q (endpointMeanCornerK 18 7 h) (endpointMeanCornerA 18 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 18 7, endpointRunWeightQ (endpointMeanCutoff 18 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 18 7) = (449198363/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 18 7 h = (logRoundedQ ((endpointMeanCutoff 18 7:ℚ)/200)).2+(449198363/1000000000000000:ℚ)+((endpointMeanRuns 18 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 18 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 18 7) r*endpointJoint24Q (endpointMeanCornerK 18 7 h) (endpointMeanCornerA 18 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 18 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 18 7 h≤endpointMeanCorner 18 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 18 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint18_07

namespace EndpointAnalyticJoint18_08
private noncomputable def weights : IntegerLookupTree := (.branch 1134 (.branch 952 (.leaf (110248980200000:ℤ)) (.leaf (13855443600000:ℤ))) (.branch 1488 (.leaf (17872578800000:ℤ)) (.branch 2116 (.leaf (12858779600000:ℤ)) (.leaf (13512446500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 145 (.leaf (1804527154568871:ℤ)) (.leaf (2202212882812189:ℤ))) (.branch 184 (.leaf (2474133428466309:ℤ)) (.branch 200 (.leaf (2809863509172591:ℤ)) (.leaf (3123332501926293:ℤ))))), (.branch 164 (.branch 145 (.leaf (1812506904997546:ℤ)) (.leaf (2220029645193378:ℤ))) (.branch 184 (.leaf (2500839512234330:ℤ)) (.branch 200 (.leaf (2849882876674645:ℤ)) (.leaf (3178035088330212:ℤ))))), (.branch 164 (.branch 145 (.leaf (1806953655222234:ℤ)) (.leaf (2208352498162256:ℤ))) (.branch 184 (.leaf (2484041393414755:ℤ)) (.branch 200 (.leaf (2825971120784575:ℤ)) (.leaf (3146910852896927:ℤ))))), (.branch 164 (.branch 145 (.leaf (1815249020008897:ℤ)) (.leaf (2226993805612205:ℤ))) (.branch 184 (.leaf (2512109105652230:ℤ)) (.branch 200 (.leaf (2868268602199850:ℤ)) (.leaf (3205038014462448:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 18 8) 8000 (endpointMeanRuns 18 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 18 8, EndpointRunConditions (endpointMeanCutoff 18 8) (endpointMeanBox 18 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 18 8 h) (endpointMeanCornerA 18 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 8, endpointJoint24Q (endpointMeanCornerK 18 8 h) (endpointMeanCornerA 18 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 18 8, endpointRunWeightQ (endpointMeanCutoff 18 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 18 8) = (223858077/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 18 8 h = (logRoundedQ ((endpointMeanCutoff 18 8:ℚ)/200)).2+(223858077/500000000000000:ℚ)+((endpointMeanRuns 18 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 18 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 18 8) r*endpointJoint24Q (endpointMeanCornerK 18 8 h) (endpointMeanCornerA 18 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 18 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 18 8 h≤endpointMeanCorner 18 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 18 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint18_08

namespace EndpointAnalyticJoint18_09
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 952 (.leaf (106323290800000:ℤ)) (.branch 1134 (.leaf (13756768800000:ℤ)) (.leaf (17758536900000:ℤ)))) (.branch 2116 (.leaf (12787027900000:ℤ)) (.branch 3283 (.leaf (4317490100000:ℤ)) (.leaf (605586800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 129 (.leaf (1812506904997546:ℤ)) (.branch 145 (.leaf (2014868512582519:ℤ)) (.leaf (2220029645193378:ℤ)))) (.branch 184 (.leaf (2500839512234330:ℤ)) (.branch 200 (.leaf (2849882876674645:ℤ)) (.leaf (3178035088330212:ℤ))))), (.branch 164 (.branch 129 (.leaf (1820521942463462:ℤ)) (.branch 145 (.leaf (2027344074713635:ℤ)) (.leaf (2237990552141255:ℤ)))) (.branch 184 (.leaf (2527833864574299:ℤ)) (.branch 200 (.leaf (2890472218401437:ℤ)) (.leaf (3233695745306967:ℤ))))), (.branch 164 (.branch 129 (.leaf (1815249020008897:ℤ)) (.branch 145 (.leaf (2019424439710255:ℤ)) (.leaf (2226993805612205:ℤ)))) (.branch 184 (.leaf (2512109105652230:ℤ)) (.branch 200 (.leaf (2868268602199850:ℤ)) (.leaf (3205038014462448:ℤ))))), (.branch 164 (.branch 129 (.leaf (1823582467165156:ℤ)) (.branch 145 (.leaf (2032438198893340:ℤ)) (.leaf (2245792469436979:ℤ)))) (.branch 184 (.leaf (2540493960942289:ℤ)) (.branch 200 (.leaf (2911199167556048:ℤ)) (.leaf (3264238853380015:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 18 9) 8000 (endpointMeanRuns 18 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 18 9, EndpointRunConditions (endpointMeanCutoff 18 9) (endpointMeanBox 18 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 18 9 h) (endpointMeanCornerA 18 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 9, endpointJoint24Q (endpointMeanCornerK 18 9 h) (endpointMeanCornerA 18 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 18 9, endpointRunWeightQ (endpointMeanCutoff 18 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 18 9) = (111563197/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 18 9 h = (logRoundedQ ((endpointMeanCutoff 18 9:ℚ)/200)).2+(111563197/250000000000000:ℚ)+((endpointMeanRuns 18 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 18 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 18 9) r*endpointJoint24Q (endpointMeanCornerK 18 9 h) (endpointMeanCornerA 18 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 18 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 18 9 h≤endpointMeanCorner 18 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 18 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint18_09

namespace EndpointAnalyticJoint18_10
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 952 (.leaf (102530222000000:ℤ)) (.branch 1134 (.leaf (13659332700000:ℤ)) (.leaf (17645926500000:ℤ)))) (.branch 2116 (.leaf (12716176800000:ℤ)) (.branch 3283 (.leaf (4296755000000:ℤ)) (.leaf (603080200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 129 (.leaf (1820521942463462:ℤ)) (.branch 145 (.leaf (2027344074713635:ℤ)) (.leaf (2237990552141255:ℤ)))) (.branch 184 (.leaf (2527833864574299:ℤ)) (.branch 200 (.leaf (2890472218401437:ℤ)) (.leaf (3233695745306967:ℤ))))), (.branch 164 (.branch 129 (.leaf (1828572423008463:ℤ)) (.branch 145 (.leaf (2039896882406686:ℤ)) (.leaf (2256096769841667:ℤ)))) (.branch 184 (.leaf (2555119597090680:ℤ)) (.branch 200 (.leaf (2931639652187834:ℤ)) (.leaf (3290331252670508:ℤ))))), (.branch 164 (.branch 129 (.leaf (1823582467165156:ℤ)) (.branch 145 (.leaf (2032438198893340:ℤ)) (.leaf (2245792469436979:ℤ)))) (.branch 184 (.leaf (2540493960942289:ℤ)) (.branch 200 (.leaf (2911199167556048:ℤ)) (.leaf (3264238853380015:ℤ))))), (.branch 164 (.branch 129 (.leaf (1831954171519593:ℤ)) (.branch 145 (.leaf (2045535822530449:ℤ)) (.leaf (2264749817924768:ℤ)))) (.branch 184 (.leaf (2569199542751765:ℤ)) (.branch 200 (.leaf (2954772292482992:ℤ)) (.leaf (3324533201738885:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 18 10) 8000 (endpointMeanRuns 18 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 18 10, EndpointRunConditions (endpointMeanCutoff 18 10) (endpointMeanBox 18 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 18 10 h) (endpointMeanCornerA 18 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 10, endpointJoint24Q (endpointMeanCornerK 18 10 h) (endpointMeanCornerA 18 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 18 10, endpointRunWeightQ (endpointMeanCutoff 18 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 18 10) = (444807791/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 18 10 h = (logRoundedQ ((endpointMeanCutoff 18 10:ℚ)/200)).2+(444807791/1000000000000000:ℚ)+((endpointMeanRuns 18 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 18 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 18 10) r*endpointJoint24Q (endpointMeanCornerK 18 10 h) (endpointMeanCornerA 18 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 18 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 18 10 h≤endpointMeanCorner 18 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 18 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint18_10

namespace EndpointAnalyticJoint18_11
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 1134 (.branch 952 (.leaf (98865053000000:ℤ)) (.leaf (13563104400000:ℤ))) (.branch 1237 (.leaf (5183347500000:ℤ)) (.leaf (9925888700000:ℤ)))) (.branch 2116 (.branch 1700 (.leaf (4753155100000:ℤ)) (.leaf (5306217600000:ℤ))) (.branch 3283 (.leaf (4276277000000:ℤ)) (.leaf (600604700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 145 (.branch 129 (.leaf (1828572423008463:ℤ)) (.leaf (2039896882406686:ℤ))) (.branch 156 (.leaf (2256096769841667:ℤ)) (.leaf (2423017536866686:ℤ)))) (.branch 184 (.branch 177 (.leaf (2555119597090680:ℤ)) (.leaf (2791663992573182:ℤ))) (.branch 200 (.leaf (2931639652187834:ℤ)) (.leaf (3290331252670508:ℤ))))), (.branch 164 (.branch 145 (.branch 129 (.leaf (1836658503364430:ℤ)) (.leaf (2052527413946887:ℤ))) (.branch 156 (.leaf (2274349473915354:ℤ)) (.leaf (2446260122312220:ℤ)))) (.branch 184 (.branch 177 (.leaf (2582699854974961:ℤ)) (.leaf (2827842342243616:ℤ))) (.branch 200 (.leaf (2973393411486641:ℤ)) (.leaf (3347958684119353:ℤ))))), (.branch 164 (.branch 145 (.branch 129 (.leaf (1831954171519593:ℤ)) (.leaf (2045535822530449:ℤ))) (.branch 156 (.leaf (2264749817924768:ℤ)) (.leaf (2434514227113337:ℤ)))) (.branch 184 (.branch 177 (.leaf (2569199542751765:ℤ)) (.leaf (2811132321214085:ℤ))) (.branch 200 (.leaf (2954772292482992:ℤ)) (.leaf (3324533201738885:ℤ))))), (.branch 164 (.branch 145 (.branch 129 (.leaf (1840364308703404:ℤ)) (.leaf (2058717851068545:ℤ))) (.branch 156 (.leaf (2283867190576230:ℤ)) (.leaf (2458924999719509:ℤ)))) (.branch 184 (.branch 177 (.leaf (2598229475037832:ℤ)) (.leaf (2849362558551198:ℤ))) (.branch 200 (.leaf (2998997594436176:ℤ)) (.leaf (3385941257950426:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 18 11) 8000 (endpointMeanRuns 18 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 18 11, EndpointRunConditions (endpointMeanCutoff 18 11) (endpointMeanBox 18 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 18 11 h) (endpointMeanCornerA 18 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 11, endpointJoint24Q (endpointMeanCornerK 18 11 h) (endpointMeanCornerA 18 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 18 11, endpointRunWeightQ (endpointMeanCutoff 18 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 18 11) = (443380707/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 18 11 h = (logRoundedQ ((endpointMeanCutoff 18 11:ℚ)/200)).2+(443380707/1000000000000000:ℚ)+((endpointMeanRuns 18 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 18 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 18 11) r*endpointJoint24Q (endpointMeanCornerK 18 11 h) (endpointMeanCornerA 18 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 18 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 18 11 h≤endpointMeanCorner 18 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 18 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint18_11

namespace EndpointAnalyticJoint18_12
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 1013 (.branch 952 (.leaf (95323249200000:ℤ)) (.leaf (4422133700000:ℤ))) (.branch 1134 (.leaf (7818177500000:ℤ)) (.branch 1237 (.leaf (5149680500000:ℤ)) (.leaf (9865451400000:ℤ))))) (.branch 2116 (.branch 1700 (.leaf (4726398800000:ℤ)) (.leaf (5278407800000:ℤ))) (.branch 2573 (.leaf (2089627500000:ℤ)) (.branch 3283 (.leaf (952279200000:ℤ)) (.leaf (598159500000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 137 (.branch 129 (.leaf (1836658503364430:ℤ)) (.leaf (2052527413946887:ℤ))) (.branch 145 (.leaf (2159561466743590:ℤ)) (.branch 156 (.leaf (2274349473915354:ℤ)) (.leaf (2446260122312220:ℤ))))) (.branch 184 (.branch 177 (.leaf (2582699854974961:ℤ)) (.leaf (2827842342243616:ℤ))) (.branch 194 (.leaf (2973393411486641:ℤ)) (.branch 200 (.leaf (3200122113888328:ℤ)) (.leaf (3347958684119353:ℤ)))))), (.branch 164 (.branch 137 (.branch 129 (.leaf (1844780340956312:ℤ)) (.leaf (2065236150580867:ℤ))) (.branch 145 (.leaf (2174895479094131:ℤ)) (.branch 156 (.leaf (2292749849494297:ℤ)) (.leaf (2469725660241577:ℤ))))) (.branch 184 (.branch 177 (.leaf (2610577817368194:ℤ)) (.leaf (2864489542387593:ℤ))) (.branch 194 (.leaf (3015741847015279:ℤ)) (.branch 200 (.leaf (3252058077296399:ℤ)) (.leaf (3406595412383745:ℤ)))))), (.branch 164 (.branch 137 (.branch 129 (.leaf (1840364308703404:ℤ)) (.leaf (2058717851068545:ℤ))) (.branch 145 (.leaf (2167256500411032:ℤ)) (.branch 156 (.leaf (2283867190576230:ℤ)) (.leaf (2458924999719509:ℤ))))) (.branch 184 (.branch 177 (.leaf (2598229475037832:ℤ)) (.leaf (2849362558551198:ℤ))) (.branch 194 (.leaf (2998997594436176:ℤ)) (.branch 200 (.leaf (3232892750232387:ℤ)) (.leaf (3385941257950426:ℤ)))))), (.branch 164 (.branch 137 (.branch 129 (.leaf (1848813055154049:ℤ)) (.leaf (2071984828437385:ℤ))) (.branch 145 (.leaf (2183292202655015:ℤ)) (.branch 156 (.leaf (2303145938199089:ℤ)) (.leaf (2483580538124375:ℤ))))) (.branch 184 (.branch 177 (.leaf (2627587422705543:ℤ)) (.leaf (2888112711310230:ℤ))) (.branch 194 (.leaf (3043884834819551:ℤ)) (.branch 200 (.leaf (3288151113189327:ℤ)) (.leaf (3448483593514549:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 18 12) 8000 (endpointMeanRuns 18 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 18 12, EndpointRunConditions (endpointMeanCutoff 18 12) (endpointMeanBox 18 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 18 12 h) (endpointMeanCornerA 18 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 12, endpointJoint24Q (endpointMeanCornerK 18 12 h) (endpointMeanCornerA 18 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 18 12, endpointRunWeightQ (endpointMeanCutoff 18 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 18 12) = (220985549/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 18 12 h = (logRoundedQ ((endpointMeanCutoff 18 12:ℚ)/200)).2+(220985549/500000000000000:ℚ)+((endpointMeanRuns 18 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 18 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 18 12) r*endpointJoint24Q (endpointMeanCornerK 18 12 h) (endpointMeanCornerA 18 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 18 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 18 12 h≤endpointMeanCorner 18 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 18 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint18_12

namespace EndpointAnalyticJoint18_13
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 1070 (.branch 952 (.leaf (91341262100000:ℤ)) (.branch 1013 (.leaf (4385175800000:ℤ)) (.leaf (3626207600000:ℤ)))) (.branch 1237 (.branch 1134 (.leaf (3626825300000:ℤ)) (.leaf (5110916500000:ℤ))) (.branch 1380 (.leaf (5662158100000:ℤ)) (.leaf (3133751300000:ℤ))))) (.branch 1943 (.branch 1587 (.leaf (2262970700000:ℤ)) (.branch 1700 (.leaf (2057583200000:ℤ)) (.leaf (3254063400000:ℤ)))) (.branch 2573 (.branch 2116 (.leaf (1349091300000:ℤ)) (.leaf (2077994900000:ℤ))) (.branch 3283 (.leaf (947371200000:ℤ)) (.leaf (595344200000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 145 (.branch 129 (.leaf (1844780340956312:ℤ)) (.branch 137 (.leaf (2065236150580867:ℤ)) (.leaf (2174895479094131:ℤ)))) (.branch 156 (.branch 149 (.leaf (2292749849494297:ℤ)) (.leaf (2355005816298511:ℤ))) (.branch 160 (.leaf (2469725660241577:ℤ)) (.leaf (2538791258106900:ℤ))))) (.branch 184 (.branch 169 (.leaf (2610577817368194:ℤ)) (.branch 177 (.leaf (2704358321122421:ℤ)) (.leaf (2864489542387593:ℤ)))) (.branch 194 (.branch 189 (.leaf (3015741847015279:ℤ)) (.leaf (3130753192150524:ℤ))) (.branch 200 (.leaf (3252058077296399:ℤ)) (.leaf (3406595412383745:ℤ)))))), (.branch 164 (.branch 145 (.branch 129 (.leaf (1852938093905216:ℤ)) (.branch 137 (.leaf (2078023576535013:ℤ)) (.leaf (2190338370927096:ℤ)))) (.branch 156 (.branch 149 (.leaf (2311299091298651:ℤ)) (.leaf (2375299282358080:ℤ))) (.branch 160 (.leaf (2493416289307109:ℤ)) (.leaf (2564639538195457:ℤ))))) (.branch 184 (.branch 169 (.leaf (2638756697727442:ℤ)) (.branch 177 (.leaf (2735714693778392:ℤ)) (.leaf (2901611669035893:ℤ)))) (.branch 194 (.branch 189 (.leaf (3058693428425921:ℤ)) (.leaf (3178379838566330:ℤ))) (.branch 200 (.leaf (3304836928631590:ℤ)) (.leaf (3466259114462912:ℤ)))))), (.branch 164 (.branch 145 (.branch 129 (.leaf (1848813055154049:ℤ)) (.branch 137 (.leaf (2071984828437385:ℤ)) (.leaf (2183292202655015:ℤ)))) (.branch 156 (.branch 149 (.leaf (2303145938199089:ℤ)) (.leaf (2366555434109701:ℤ))) (.branch 160 (.leaf (2483580538124375:ℤ)) (.leaf (2554147912760023:ℤ))))) (.branch 184 (.branch 169 (.leaf (2627587422705543:ℤ)) (.branch 177 (.leaf (2723670259247447:ℤ)) (.leaf (2888112711310230:ℤ)))) (.branch 194 (.branch 189 (.leaf (3043884834819551:ℤ)) (.leaf (3162628797441781:ℤ))) (.branch 200 (.leaf (3288151113189327:ℤ)) (.leaf (3448483593514549:ℤ)))))), (.branch 164 (.branch 145 (.branch 129 (.leaf (1857300588119004:ℤ)) (.branch 137 (.leaf (2085337302071980:ℤ)) (.leaf (2199446554328085:ℤ)))) (.branch 156 (.branch 149 (.leaf (2322587423003620:ℤ)) (.leaf (2387846875795129:ℤ))) (.branch 160 (.leaf (2508483296584386:ℤ)) (.leaf (2581349731663222:ℤ))))) (.branch 184 (.branch 169 (.leaf (2657277092070487:ℤ)) (.branch 177 (.leaf (2756759072917095:ℤ)) (.leaf (2927389850125970:ℤ)))) (.branch 194 (.branch 189 (.leaf (3089443921140034:ℤ)) (.leaf (3213243226853978:ℤ))) (.branch 200 (.leaf (3344353982169999:ℤ)) (.leaf (3512181159911048:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 18 13) 8000 (endpointMeanRuns 18 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 18 13, EndpointRunConditions (endpointMeanCutoff 18 13) (endpointMeanBox 18 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 18 13 h) (endpointMeanCornerA 18 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 13, endpointJoint24Q (endpointMeanCornerK 18 13 h) (endpointMeanCornerA 18 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 18 13, endpointRunWeightQ (endpointMeanCutoff 18 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 18 13) = (220174039/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 18 13 h = (logRoundedQ ((endpointMeanCutoff 18 13:ℚ)/200)).2+(220174039/500000000000000:ℚ)+((endpointMeanRuns 18 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 18 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 18 13) r*endpointJoint24Q (endpointMeanCornerK 18 13 h) (endpointMeanCornerA 18 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 18 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 18 13 h≤endpointMeanCorner 18 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 18 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint18_13

namespace EndpointAnalyticJoint18_14
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 1134 (.branch 972 (.branch 952 (.leaf (88052030000000:ℤ)) (.leaf (1410972700000:ℤ))) (.branch 1013 (.leaf (2800913500000:ℤ)) (.branch 1070 (.leaf (3601227400000:ℤ)) (.leaf (3602627400000:ℤ))))) (.branch 1237 (.branch 1176 (.leaf (2070421000000:ℤ)) (.leaf (2754690100000:ℤ))) (.branch 1287 (.leaf (1986640500000:ℤ)) (.branch 1380 (.leaf (3302107800000:ℤ)) (.leaf (3115516000000:ℤ)))))) (.branch 2116 (.branch 1700 (.branch 1587 (.leaf (2250240000000:ℤ)) (.leaf (2046358700000:ℤ))) (.branch 1796 (.leaf (1353110000000:ℤ)) (.branch 1943 (.leaf (1626089600000:ℤ)) (.leaf (1342374000000:ℤ))))) (.branch 2885 (.branch 2322 (.leaf (1046783100000:ℤ)) (.branch 2573 (.leaf (762942700000:ℤ)) (.leaf (501604600000:ℤ)))) (.branch 3283 (.leaf (285948700000:ℤ)) (.branch 4533 (.leaf (232859000000:ℤ)) (.leaf (20346600000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 160 (.branch 141 (.branch 129 (.branch 121 (.leaf (1852938093905216:ℤ)) (.leaf (1973556557244394:ℤ))) (.branch 133 (.leaf (2078023576535013:ℤ)) (.branch 137 (.leaf (2133152391674789:ℤ)) (.leaf (2190338370927096:ℤ))))) (.branch 149 (.branch 145 (.leaf (2249684200885069:ℤ)) (.leaf (2311299091298651:ℤ))) (.branch 153 (.leaf (2375299282358080:ℤ)) (.branch 156 (.leaf (2441808598908562:ℤ)) (.leaf (2493416289307109:ℤ)))))) (.branch 181 (.branch 169 (.branch 164 (.leaf (2564639538195457:ℤ)) (.leaf (2638756697727442:ℤ))) (.branch 174 (.leaf (2735714693778392:ℤ)) (.branch 177 (.leaf (2837775764466051:ℤ)) (.leaf (2901611669035893:ℤ))))) (.branch 194 (.branch 184 (.leaf (2989932350254745:ℤ)) (.branch 189 (.leaf (3058693428425921:ℤ)) (.leaf (3178379838566330:ℤ)))) (.branch 198 (.leaf (3304836928631590:ℤ)) (.branch 200 (.leaf (3411225566708464:ℤ)) (.leaf (3466259114462912:ℤ))))))), (.branch 160 (.branch 141 (.branch 129 (.branch 121 (.leaf (1861131921031457:ℤ)) (.leaf (1984134489538023:ℤ))) (.branch 133 (.leaf (2090890179033929:ℤ)) (.branch 137 (.leaf (2147308570749727:ℤ)) (.leaf (2205890915343580:ℤ))))) (.branch 149 (.branch 145 (.leaf (2266748144898236:ℤ)) (.leaf (2329998403714323:ℤ))) (.branch 153 (.leaf (2395767620497317:ℤ)) (.branch 156 (.leaf (2464190134410782:ℤ)) (.leaf (2517334168676006:ℤ)))))) (.branch 181 (.branch 169 (.branch 164 (.leaf (2590750988239955:ℤ)) (.leaf (2667239744196214:ℤ))) (.branch 174 (.leaf (2767434635898685:ℤ)) (.branch 177 (.leaf (2873064343000803:ℤ)) (.leaf (2939214876961158:ℤ))))) (.branch 194 (.branch 184 (.leaf (3030840888399305:ℤ)) (.branch 189 (.leaf (3102256745999425:ℤ)) (.leaf (3226731006306422:ℤ)))) (.branch 198 (.leaf (3358472347433310:ℤ)) (.branch 200 (.leaf (3469482052268018:ℤ)) (.leaf (3526967776954127:ℤ))))))), (.branch 160 (.branch 141 (.branch 129 (.branch 121 (.leaf (1857300588119004:ℤ)) (.leaf (1979395355706835:ℤ))) (.branch 133 (.leaf (2085337302071980:ℤ)) (.branch 137 (.leaf (2141319574238084:ℤ)) (.leaf (2199446554328085:ℤ))))) (.branch 149 (.branch 145 (.leaf (2259829582350918:ℤ)) (.leaf (2322587423003620:ℤ))) (.branch 153 (.leaf (2387846875795129:ℤ)) (.branch 156 (.leaf (2455743445110325:ℤ)) (.leaf (2508483296584386:ℤ)))))) (.branch 181 (.branch 169 (.branch 164 (.leaf (2581349731663222:ℤ)) (.leaf (2657277092070487:ℤ))) (.branch 174 (.leaf (2756759072917095:ℤ)) (.branch 177 (.leaf (2861669936492157:ℤ)) (.leaf (2927389850125970:ℤ))))) (.branch 194 (.branch 184 (.leaf (3018447126802867:ℤ)) (.branch 189 (.leaf (3089443921140034:ℤ)) (.leaf (3213243226853978:ℤ)))) (.branch 198 (.leaf (3344353982169999:ℤ)) (.branch 200 (.leaf (3454905112251307:ℤ)) (.leaf (3512181159911048:ℤ))))))), (.branch 160 (.branch 141 (.branch 129 (.branch 121 (.leaf (1865827085659437:ℤ)) (.leaf (1990424539307095:ℤ))) (.branch 133 (.leaf (2098775822935164:ℤ)) (.branch 137 (.leaf (2156118397600093:ℤ)) (.leaf (2215720433326755:ℤ))))) (.branch 149 (.branch 145 (.leaf (2277702407799018:ℤ)) (.leaf (2342193018698885:ℤ))) (.branch 153 (.leaf (2409329872464872:ℤ)) (.branch 156 (.leaf (2479260241865058:ℤ)) (.leaf (2533635753964729:ℤ)))))) (.branch 181 (.branch 169 (.branch 164 (.leaf (2608841251467424:ℤ)) (.leaf (2687302231326704:ℤ))) (.branch 174 (.leaf (2790249869751315:ℤ)) (.branch 177 (.leaf (2898991370415268:ℤ)) (.leaf (2967201141790904:ℤ))))) (.branch 194 (.branch 184 (.leaf (3061820961235850:ℤ)) (.branch 189 (.leaf (3135684909194320:ℤ)) (.leaf (3264667685083593:ℤ)))) (.branch 198 (.leaf (3401517501185571:ℤ)) (.branch 200 (.leaf (3517102483196249:ℤ)) (.leaf (3577055295618326:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 18 14) 8000 (endpointMeanRuns 18 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 18 14, EndpointRunConditions (endpointMeanCutoff 18 14) (endpointMeanBox 18 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 18 14 h) (endpointMeanCornerA 18 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 14, endpointJoint24Q (endpointMeanCornerK 18 14 h) (endpointMeanCornerA 18 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 18 14, endpointRunWeightQ (endpointMeanCutoff 18 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 18 14) = (438974901/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 18 14 h = (logRoundedQ ((endpointMeanCutoff 18 14:ℚ)/200)).2+(438974901/1000000000000000:ℚ)+((endpointMeanRuns 18 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 18 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 18 14) r*endpointJoint24Q (endpointMeanCornerK 18 14 h) (endpointMeanCornerA 18 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 18 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 18 14 h≤endpointMeanCorner 18 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 18 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint18_14

namespace EndpointAnalyticJoint18_15
private noncomputable def weights : IntegerLookupTree := (.branch 1443 (.branch 1134 (.branch 1013 (.branch 952 (.leaf (84872939300000:ℤ)) (.branch 972 (.leaf (1400840600000:ℤ)) (.leaf (2781167300000:ℤ)))) (.branch 1070 (.branch 1035 (.leaf (1372432000000:ℤ)) (.leaf (2094891700000:ℤ))) (.branch 1095 (.leaf (1392622800000:ℤ)) (.leaf (2068608500000:ℤ))))) (.branch 1237 (.branch 1176 (.leaf (2057040000000:ℤ)) (.branch 1205 (.leaf (1304365200000:ℤ)) (.leaf (1353116200000:ℤ)))) (.branch 1341 (.branch 1287 (.leaf (1974395000000:ℤ)) (.leaf (1916958600000:ℤ))) (.branch 1380 (.leaf (1235425500000:ℤ)) (.leaf (1824220200000:ℤ)))))) (.branch 1943 (.branch 1587 (.branch 1488 (.leaf (1140132800000:ℤ)) (.branch 1536 (.leaf (1100586800000:ℤ)) (.leaf (1050766600000:ℤ)))) (.branch 1700 (.branch 1642 (.leaf (1009624300000:ℤ)) (.leaf (940879900000:ℤ))) (.branch 1796 (.leaf (1345980800000:ℤ)) (.leaf (1617764700000:ℤ))))) (.branch 2573 (.branch 2116 (.leaf (1335735800000:ℤ)) (.branch 2322 (.leaf (1041791200000:ℤ)) (.leaf (759440800000:ℤ)))) (.branch 3283 (.branch 2885 (.leaf (499393800000:ℤ)) (.leaf (284741800000:ℤ))) (.branch 4533 (.leaf (231930100000:ℤ)) (.leaf (20273200000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 149 (.branch 133 (.branch 121 (.leaf (1861131921031457:ℤ)) (.branch 129 (.leaf (1984134489538023:ℤ)) (.leaf (2090890179033929:ℤ)))) (.branch 141 (.branch 137 (.leaf (2147308570749727:ℤ)) (.leaf (2205890915343580:ℤ))) (.branch 145 (.leaf (2266748144898236:ℤ)) (.leaf (2329998403714323:ℤ))))) (.branch 158 (.branch 153 (.leaf (2395767620497317:ℤ)) (.branch 156 (.leaf (2464190134410782:ℤ)) (.leaf (2517334168676006:ℤ)))) (.branch 162 (.branch 160 (.leaf (2553668917063685:ℤ)) (.leaf (2590750988239955:ℤ))) (.branch 164 (.leaf (2628600866382160:ℤ)) (.leaf (2667239744196214:ℤ)))))) (.branch 184 (.branch 174 (.branch 169 (.leaf (2706689552648969:ℤ)) (.branch 171 (.leaf (2767434635898685:ℤ)) (.leaf (2809012849561318:ℤ)))) (.branch 179 (.branch 177 (.leaf (2873064343000803:ℤ)) (.leaf (2939214876961158:ℤ))) (.branch 181 (.leaf (2984526699335359:ℤ)) (.leaf (3030840888399305:ℤ))))) (.branch 192 (.branch 187 (.leaf (3102256745999425:ℤ)) (.branch 189 (.leaf (3176099632288812:ℤ)) (.leaf (3226731006306422:ℤ)))) (.branch 198 (.branch 194 (.leaf (3304868209114208:ℤ)) (.leaf (3358472347433310:ℤ))) (.branch 200 (.leaf (3469482052268018:ℤ)) (.leaf (3526967776954127:ℤ))))))), (.branch 166 (.branch 149 (.branch 133 (.branch 121 (.leaf (1869361981857681:ℤ)) (.branch 129 (.leaf (1994769117775432:ℤ)) (.leaf (2103836448318986:ℤ)))) (.branch 141 (.branch 137 (.leaf (2161558694076736:ℤ)) (.leaf (2221553890934096:ℤ))) (.branch 145 (.leaf (2283941519604455:ℤ)) (.leaf (2348849000871178:ℤ))))) (.branch 158 (.branch 153 (.leaf (2416412337617207:ℤ)) (.branch 156 (.leaf (2486776818314746:ℤ)) (.leaf (2541481478227089:ℤ)))) (.branch 162 (.branch 160 (.leaf (2578909212929420:ℤ)) (.leaf (2617128287661435:ℤ))) (.branch 164 (.leaf (2656160951466830:ℤ)) (.leaf (2696030239978838:ℤ)))))) (.branch 184 (.branch 174 (.branch 169 (.leaf (2736760009056104:ℤ)) (.branch 171 (.leaf (2799522362982221:ℤ)) (.leaf (2842513409232883:ℤ)))) (.branch 179 (.branch 177 (.leaf (2908791745416775:ℤ)) (.leaf (2977305400698304:ℤ))) (.branch 181 (.leaf (3024272559075541:ℤ)) (.leaf (3072309141044759:ℤ))))) (.branch 192 (.branch 187 (.leaf (3146440512363376:ℤ)) (.branch 189 (.leaf (3223166218623370:ℤ)) (.leaf (3275817717166149:ℤ)))) (.branch 198 (.branch 194 (.leaf (3357140945653022:ℤ)) (.leaf (3412978235251252:ℤ))) (.branch 200 (.leaf (3528733434835519:ℤ)) (.leaf (3588739701475022:ℤ))))))), (.branch 166 (.branch 149 (.branch 133 (.branch 121 (.leaf (1865827085659437:ℤ)) (.branch 129 (.leaf (1990424539307095:ℤ)) (.leaf (2098775822935164:ℤ)))) (.branch 141 (.branch 137 (.leaf (2156118397600093:ℤ)) (.leaf (2215720433326755:ℤ))) (.branch 145 (.leaf (2277702407799018:ℤ)) (.leaf (2342193018698885:ℤ))))) (.branch 158 (.branch 153 (.leaf (2409329872464872:ℤ)) (.branch 156 (.leaf (2479260241865058:ℤ)) (.leaf (2533635753964729:ℤ)))) (.branch 162 (.branch 160 (.leaf (2570843016419036:ℤ)) (.leaf (2608841251467424:ℤ))) (.branch 164 (.leaf (2647653149986029:ℤ)) (.leaf (2687302231326704:ℤ)))))) (.branch 184 (.branch 174 (.branch 169 (.leaf (2727812880233096:ℤ)) (.branch 171 (.leaf (2790249869751315:ℤ)) (.leaf (2833027156273281:ℤ)))) (.branch 179 (.branch 177 (.leaf (2898991370415268:ℤ)) (.leaf (2967201141790904:ℤ))) (.branch 181 (.leaf (3013972889650599:ℤ)) (.leaf (3061820961235850:ℤ))))) (.branch 192 (.branch 187 (.leaf (3135684909194320:ℤ)) (.branch 189 (.leaf (3212165255892729:ℤ)) (.leaf (3264667685083593:ℤ)))) (.branch 198 (.branch 194 (.leaf (3345792828730453:ℤ)) (.leaf (3401517501185571:ℤ))) (.branch 200 (.leaf (3517102483196249:ℤ)) (.leaf (3577055295618326:ℤ))))))), (.branch 166 (.branch 149 (.branch 133 (.branch 121 (.leaf (1874392726653960:ℤ)) (.branch 129 (.leaf (2001515177477581:ℤ)) (.leaf (2112300945540335:ℤ)))) (.branch 141 (.branch 137 (.leaf (2171019496762288:ℤ)) (.leaf (2232114724043152:ℤ))) (.branch 145 (.leaf (2295716588105019:ℤ)) (.leaf (2361964110589794:ℤ))))) (.branch 158 (.branch 153 (.leaf (2431006147502077:ℤ)) (.branch 156 (.leaf (2503002241187558:ℤ)) (.leaf (2559040413986055:ℤ)))) (.branch 162 (.branch 160 (.leaf (2597413455043760:ℤ)) (.leaf (2636625557503535:ℤ))) (.branch 164 (.leaf (2676701412183026:ℤ)) (.leaf (2717666631019869:ℤ)))))) (.branch 184 (.branch 174 (.branch 169 (.leaf (2759547788875261:ℤ)) (.branch 171 (.leaf (2824147533287675:ℤ)) (.leaf (2868441526808363:ℤ)))) (.branch 179 (.branch 177 (.leaf (2936799544410077:ℤ)) (.leaf (3007553850562944:ℤ))) (.branch 181 (.leaf (3056110550994394:ℤ)) (.leaf (3105818059696457:ℤ))))) (.branch 192 (.branch 187 (.leaf (3182618005288379:ℤ)) (.branch 189 (.leaf (3262221028796488:ℤ)) (.leaf (3316915135759627:ℤ)))) (.branch 198 (.branch 194 (.leaf (3401502560360894:ℤ)) (.leaf (3459658090189455:ℤ))) (.branch 200 (.leaf (3580419570262696:ℤ)) (.leaf (3643127733261674:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 18 15) 8000 (endpointMeanRuns 18 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 18 15, EndpointRunConditions (endpointMeanCutoff 18 15) (endpointMeanBox 18 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 18 15 h) (endpointMeanCornerA 18 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 15, endpointJoint24Q (endpointMeanCornerK 18 15 h) (endpointMeanCornerA 18 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 18 15, endpointRunWeightQ (endpointMeanCutoff 18 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 18 15) = (54702239/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 18 15 h = (logRoundedQ ((endpointMeanCutoff 18 15:ℚ)/200)).2+(54702239/125000000000000:ℚ)+((endpointMeanRuns 18 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 18 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 18 15) r*endpointJoint24Q (endpointMeanCornerK 18 15 h) (endpointMeanCornerA 18 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 18 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 18 15 h≤endpointMeanCorner 18 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 18 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint18_15

namespace EndpointAnalyticJoint18_16
private noncomputable def weights : IntegerLookupTree := (.branch 1443 (.branch 1134 (.branch 1013 (.branch 952 (.leaf (81800145200000:ℤ)) (.branch 972 (.leaf (1390826600000:ℤ)) (.leaf (2761651200000:ℤ)))) (.branch 1070 (.branch 1035 (.leaf (1362983000000:ℤ)) (.leaf (2080695900000:ℤ))) (.branch 1095 (.leaf (1383339400000:ℤ)) (.leaf (2055042000000:ℤ))))) (.branch 1237 (.branch 1176 (.leaf (2043814800000:ℤ)) (.branch 1205 (.leaf (1296118800000:ℤ)) (.leaf (1344677200000:ℤ)))) (.branch 1341 (.branch 1287 (.leaf (1962292100000:ℤ)) (.leaf (1905452000000:ℤ))) (.branch 1380 (.leaf (1228142100000:ℤ)) (.leaf (1813658800000:ℤ)))))) (.branch 1867 (.branch 1587 (.branch 1488 (.leaf (1133654700000:ℤ)) (.branch 1536 (.leaf (1094427100000:ℤ)) (.leaf (1044975300000:ℤ)))) (.branch 1700 (.branch 1642 (.leaf (1004146100000:ℤ)) (.leaf (935855200000:ℤ))) (.branch 1796 (.leaf (1338934600000:ℤ)) (.leaf (803307000000:ℤ))))) (.branch 2573 (.branch 2116 (.branch 1943 (.leaf (729308300000:ℤ)) (.leaf (1329175100000:ℤ))) (.branch 2322 (.leaf (1036857500000:ℤ)) (.leaf (755979600000:ℤ)))) (.branch 3283 (.branch 2885 (.leaf (497208700000:ℤ)) (.leaf (283549000000:ℤ))) (.branch 4533 (.leaf (231012000000:ℤ)) (.leaf (20200600000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 149 (.branch 133 (.branch 121 (.leaf (1869361981857681:ℤ)) (.branch 129 (.leaf (1994769117775432:ℤ)) (.leaf (2103836448318986:ℤ)))) (.branch 141 (.branch 137 (.leaf (2161558694076736:ℤ)) (.leaf (2221553890934096:ℤ))) (.branch 145 (.leaf (2283941519604455:ℤ)) (.leaf (2348849000871178:ℤ))))) (.branch 156 (.branch 151 (.leaf (2416412337617207:ℤ)) (.branch 153 (.leaf (2451234971120284:ℤ)) (.leaf (2486776818314746:ℤ)))) (.branch 160 (.branch 158 (.leaf (2541481478227089:ℤ)) (.leaf (2578909212929420:ℤ))) (.branch 162 (.leaf (2617128287661435:ℤ)) (.leaf (2656160951466830:ℤ)))))) (.branch 181 (.branch 171 (.branch 166 (.leaf (2696030239978838:ℤ)) (.branch 169 (.leaf (2736760009056104:ℤ)) (.leaf (2799522362982221:ℤ)))) (.branch 177 (.branch 174 (.leaf (2842513409232883:ℤ)) (.leaf (2908791745416775:ℤ))) (.branch 179 (.leaf (2977305400698304:ℤ)) (.leaf (3024272559075541:ℤ))))) (.branch 192 (.branch 187 (.branch 184 (.leaf (3072309141044759:ℤ)) (.leaf (3146440512363376:ℤ))) (.branch 189 (.leaf (3223166218623370:ℤ)) (.leaf (3275817717166149:ℤ)))) (.branch 198 (.branch 194 (.leaf (3357140945653022:ℤ)) (.leaf (3412978235251252:ℤ))) (.branch 200 (.leaf (3528733434835519:ℤ)) (.leaf (3588739701475022:ℤ))))))), (.branch 164 (.branch 149 (.branch 133 (.branch 121 (.leaf (1877628436611942:ℤ)) (.branch 129 (.leaf (2005460745837368:ℤ)) (.leaf (2116862877667006:ℤ)))) (.branch 141 (.branch 137 (.leaf (2175903385095420:ℤ)) (.leaf (2237328081817555:ℤ))) (.branch 145 (.leaf (2301265306740684:ℤ)) (.leaf (2367852106721858:ℤ))))) (.branch 156 (.branch 151 (.leaf (2437234953603962:ℤ)) (.branch 153 (.leaf (2473023436297820:ℤ)) (.leaf (2509570531003809:ℤ)))) (.branch 160 (.branch 158 (.leaf (2565860418749462:ℤ)) (.leaf (2604398982221846:ℤ))) (.branch 162 (.leaf (2643774143161036:ℤ)) (.leaf (2684009995708281:ℤ)))))) (.branch 181 (.branch 171 (.branch 166 (.leaf (2725131503718938:ℤ)) (.branch 169 (.leaf (2767164538629347:ℤ)) (.leaf (2831982139405619:ℤ)))) (.branch 177 (.branch 174 (.leaf (2876413499828089:ℤ)) (.leaf (2944963428618346:ℤ))) (.branch 179 (.leaf (3015889555578224:ℤ)) (.leaf (3064547726650974:ℤ))))) (.branch 192 (.branch 187 (.branch 184 (.leaf (3114344766258014:ℤ)) (.leaf (3191253564234602:ℤ))) (.branch 189 (.leaf (3270930284195247:ℤ)) (.leaf (3325651160610127:ℤ)))) (.branch 198 (.branch 194 (.leaf (3410240474309513:ℤ)) (.leaf (3468368719248485:ℤ))) (.branch 200 (.leaf (3588996705138213:ℤ)) (.leaf (3651593510180961:ℤ))))))), (.branch 164 (.branch 149 (.branch 133 (.branch 121 (.leaf (1874392726653960:ℤ)) (.branch 129 (.leaf (2001515177477581:ℤ)) (.leaf (2112300945540335:ℤ)))) (.branch 141 (.branch 137 (.leaf (2171019496762288:ℤ)) (.leaf (2232114724043152:ℤ))) (.branch 145 (.leaf (2295716588105019:ℤ)) (.leaf (2361964110589794:ℤ))))) (.branch 156 (.branch 151 (.leaf (2431006147502077:ℤ)) (.branch 153 (.leaf (2466624523363487:ℤ)) (.leaf (2503002241187558:ℤ)))) (.branch 160 (.branch 158 (.leaf (2559040413986055:ℤ)) (.leaf (2597413455043760:ℤ))) (.branch 162 (.leaf (2636625557503535:ℤ)) (.leaf (2676701412183026:ℤ)))))) (.branch 181 (.branch 171 (.branch 166 (.leaf (2717666631019869:ℤ)) (.branch 169 (.leaf (2759547788875261:ℤ)) (.leaf (2824147533287675:ℤ)))) (.branch 177 (.branch 174 (.leaf (2868441526808363:ℤ)) (.leaf (2936799544410077:ℤ))) (.branch 179 (.leaf (3007553850562944:ℤ)) (.leaf (3056110550994394:ℤ))))) (.branch 192 (.branch 187 (.branch 184 (.leaf (3105818059696457:ℤ)) (.leaf (3182618005288379:ℤ))) (.branch 189 (.leaf (3262221028796488:ℤ)) (.leaf (3316915135759627:ℤ)))) (.branch 198 (.branch 194 (.leaf (3401502560360894:ℤ)) (.leaf (3459658090189455:ℤ))) (.branch 200 (.leaf (3580419570262696:ℤ)) (.leaf (3643127733261674:ℤ))))))), (.branch 164 (.branch 149 (.branch 133 (.branch 121 (.leaf (1882997690802386:ℤ)) (.branch 129 (.leaf (2012667612642929:ℤ)) (.leaf (2125913227974338:ℤ)))) (.branch 141 (.branch 137 (.leaf (2186023578560539:ℤ)) (.leaf (2248630317413104:ℤ))) (.branch 145 (.leaf (2313873241234063:ℤ)) (.leaf (2381902095675005:ℤ))))) (.branch 156 (.branch 151 (.leaf (2452877439794850:ℤ)) (.branch 153 (.leaf (2489523409663064:ℤ)) (.leaf (2526971599672398:ℤ)))) (.branch 160 (.branch 158 (.leaf (2584699805473733:ℤ)) (.leaf (2624258507172379:ℤ))) (.branch 162 (.leaf (2664705767961376:ℤ)) (.leaf (2706068372294316:ℤ)))))) (.branch 181 (.branch 171 (.branch 166 (.leaf (2748374124525847:ℤ)) (.branch 169 (.leaf (2791651896018476:ℤ)) (.leaf (2858457006391942:ℤ)))) (.branch 177 (.branch 174 (.leaf (2904298596114484:ℤ)) (.leaf (2975100806461453:ℤ))) (.branch 179 (.leaf (3048455339490905:ℤ)) (.leaf (3098837329284003:ℤ))))) (.branch 192 (.branch 187 (.branch 184 (.leaf (3150447378230499:ℤ)) (.leaf (3230253568490183:ℤ))) (.branch 189 (.leaf (3313056830186140:ℤ)) (.leaf (3369998749979847:ℤ)))) (.branch 198 (.branch 194 (.leaf (3458139897003721:ℤ)) (.leaf (3518792449793823:ℤ))) (.branch 200 (.leaf (3644876531283267:ℤ)) (.leaf (3710420606893662:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 18 16) 8000 (endpointMeanRuns 18 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 18 16, EndpointRunConditions (endpointMeanCutoff 18 16) (endpointMeanBox 18 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 18 16 h) (endpointMeanCornerA 18 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 16, endpointJoint24Q (endpointMeanCornerK 18 16 h) (endpointMeanCornerA 18 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 18 16, endpointRunWeightQ (endpointMeanCutoff 18 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 18 16) = (109069183/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 18 16 h = (logRoundedQ ((endpointMeanCutoff 18 16:ℚ)/200)).2+(109069183/250000000000000:ℚ)+((endpointMeanRuns 18 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 18 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 18 16) r*endpointJoint24Q (endpointMeanCornerK 18 16 h) (endpointMeanCornerA 18 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 18 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 18 16 h≤endpointMeanCorner 18 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 18 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint18_16

namespace EndpointAnalyticJoint18_17
private noncomputable def weights : IntegerLookupTree := (.branch 1380 (.branch 1095 (.branch 1013 (.branch 952 (.leaf (78829949700000:ℤ)) (.branch 972 (.leaf (1380927900000:ℤ)) (.leaf (2742359800000:ℤ)))) (.branch 1035 (.leaf (1353642900000:ℤ)) (.branch 1070 (.leaf (2066663600000:ℤ)) (.leaf (1374162900000:ℤ))))) (.branch 1237 (.branch 1134 (.leaf (2041631800000:ℤ)) (.branch 1176 (.leaf (2030742000000:ℤ)) (.leaf (2703113400000:ℤ)))) (.branch 1287 (.leaf (1950328700000:ℤ)) (.branch 1341 (.leaf (1894077800000:ℤ)) (.leaf (1220942500000:ℤ)))))) (.branch 1943 (.branch 1587 (.branch 1443 (.leaf (1803219100000:ℤ)) (.branch 1488 (.leaf (1127251200000:ℤ)) (.leaf (2212934300000:ℤ)))) (.branch 1700 (.leaf (2013467200000:ℤ)) (.branch 1796 (.leaf (1331969600000:ℤ)) (.leaf (1601403700000:ℤ))))) (.branch 2573 (.branch 2116 (.leaf (1322689800000:ℤ)) (.branch 2322 (.leaf (1031980600000:ℤ)) (.leaf (752558400000:ℤ)))) (.branch 3283 (.branch 2885 (.leaf (495048800000:ℤ)) (.leaf (282369900000:ℤ))) (.branch 4533 (.leaf (230104400000:ℤ)) (.leaf (20128900000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 145 (.branch 133 (.branch 121 (.leaf (1877628436611942:ℤ)) (.branch 129 (.leaf (2005460745837368:ℤ)) (.leaf (2116862877667006:ℤ)))) (.branch 137 (.leaf (2175903385095420:ℤ)) (.branch 141 (.leaf (2237328081817555:ℤ)) (.leaf (2301265306740684:ℤ))))) (.branch 156 (.branch 149 (.leaf (2367852106721858:ℤ)) (.branch 153 (.leaf (2437234953603962:ℤ)) (.leaf (2509570531003809:ℤ)))) (.branch 160 (.leaf (2565860418749462:ℤ)) (.branch 164 (.leaf (2643774143161036:ℤ)) (.leaf (2725131503718938:ℤ)))))) (.branch 184 (.branch 174 (.branch 169 (.leaf (2767164538629347:ℤ)) (.branch 171 (.leaf (2831982139405619:ℤ)) (.leaf (2876413499828089:ℤ)))) (.branch 177 (.leaf (2944963428618346:ℤ)) (.branch 181 (.leaf (3015889555578224:ℤ)) (.leaf (3114344766258014:ℤ))))) (.branch 192 (.branch 187 (.leaf (3191253564234602:ℤ)) (.branch 189 (.leaf (3270930284195247:ℤ)) (.leaf (3325651160610127:ℤ)))) (.branch 198 (.branch 194 (.leaf (3410240474309513:ℤ)) (.leaf (3468368719248485:ℤ))) (.branch 200 (.leaf (3588996705138213:ℤ)) (.leaf (3651593510180961:ℤ))))))), (.branch 166 (.branch 145 (.branch 133 (.branch 121 (.leaf (1885931446230841:ℤ)) (.branch 129 (.leaf (2016209679233336:ℤ)) (.leaf (2129969963409057:ℤ)))) (.branch 137 (.leaf (2190343271382672:ℤ)) (.branch 141 (.leaf (2253214277680519:ℤ)) (.leaf (2318720495490379:ℤ))))) (.branch 156 (.branch 149 (.leaf (2387008955121268:ℤ)) (.branch 153 (.leaf (2458237001440896:ℤ)) (.leaf (2532573170096852:ℤ)))) (.branch 160 (.leaf (2590473212143111:ℤ)) (.branch 164 (.leaf (2670691288997701:ℤ)) (.leaf (2754546889881967:ℤ)))))) (.branch 184 (.branch 174 (.branch 169 (.leaf (2797906852814876:ℤ)) (.branch 171 (.leaf (2864818278989889:ℤ)) (.leaf (2910717886191483:ℤ)))) (.branch 177 (.leaf (2981584917368117:ℤ)) (.branch 181 (.leaf (3054973738774840:ℤ)) (.leaf (3156955526884395:ℤ))))) (.branch 192 (.branch 187 (.leaf (3236704864186513:ℤ)) (.branch 189 (.leaf (3319402164941778:ℤ)) (.leaf (3376242696322935:ℤ)))) (.branch 198 (.branch 194 (.leaf (3464179872363561:ℤ)) (.leaf (3524658155863052:ℤ))) (.branch 200 (.leaf (3650289144068864:ℤ)) (.leaf (3715548151378932:ℤ))))))), (.branch 166 (.branch 145 (.branch 133 (.branch 121 (.leaf (1882997690802386:ℤ)) (.branch 129 (.leaf (2012667612642929:ℤ)) (.leaf (2125913227974338:ℤ)))) (.branch 137 (.leaf (2186023578560539:ℤ)) (.branch 141 (.leaf (2248630317413104:ℤ)) (.leaf (2313873241234063:ℤ))))) (.branch 156 (.branch 149 (.leaf (2381902095675005:ℤ)) (.branch 153 (.leaf (2452877439794850:ℤ)) (.leaf (2526971599672398:ℤ)))) (.branch 160 (.leaf (2584699805473733:ℤ)) (.branch 164 (.leaf (2664705767961376:ℤ)) (.leaf (2748374124525847:ℤ)))))) (.branch 184 (.branch 174 (.branch 169 (.leaf (2791651896018476:ℤ)) (.branch 171 (.leaf (2858457006391942:ℤ)) (.leaf (2904298596114484:ℤ)))) (.branch 177 (.leaf (2975100806461453:ℤ)) (.branch 181 (.leaf (3048455339490905:ℤ)) (.leaf (3150447378230499:ℤ))))) (.branch 192 (.branch 187 (.leaf (3230253568490183:ℤ)) (.branch 189 (.leaf (3313056830186140:ℤ)) (.leaf (3369998749979847:ℤ)))) (.branch 198 (.branch 194 (.leaf (3458139897003721:ℤ)) (.leaf (3518792449793823:ℤ))) (.branch 200 (.leaf (3644876531283267:ℤ)) (.leaf (3710420606893662:ℤ))))))), (.branch 166 (.branch 145 (.branch 133 (.branch 121 (.leaf (1891642158629496:ℤ)) (.branch 129 (.leaf (2023882189135767:ℤ)) (.leaf (2139613231920490:ℤ)))) (.branch 137 (.leaf (2201131354715724:ℤ)) (.branch 141 (.leaf (2265268110964530:ℤ)) (.leaf (2332173493993205:ℤ))))) (.branch 156 (.branch 149 (.leaf (2402008382745619:ℤ)) (.branch 153 (.leaf (2474945503875736:ℤ)) (.leaf (2551170494566248:ℤ)))) (.branch 160 (.leaf (2610616482609541:ℤ)) (.branch 164 (.leaf (2693085034239682:ℤ)) (.leaf (2779428588534629:ℤ)))))) (.branch 184 (.branch 174 (.branch 169 (.leaf (2824129496854973:ℤ)) (.branch 171 (.leaf (2893183291978850:ℤ)) (.leaf (2940603898165530:ℤ)))) (.branch 177 (.leaf (3013901587343625:ℤ)) (.branch 181 (.leaf (3089913071758022:ℤ)) (.leaf (3195718001578452:ℤ))))) (.branch 192 (.branch 187 (.leaf (3278602112916188:ℤ)) (.branch 189 (.leaf (3364684815391701:ℤ)) (.leaf (3423931909631090:ℤ)))) (.branch 198 (.branch 194 (.leaf (3515720283914798:ℤ)) (.leaf (3578937566066811:ℤ))) (.branch 200 (.leaf (3710493886984535:ℤ)) (.leaf (3778956459408964:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 18 17) 8000 (endpointMeanRuns 18 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 18 17, EndpointRunConditions (endpointMeanCutoff 18 17) (endpointMeanBox 18 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 18 17 h) (endpointMeanCornerA 18 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 17, endpointJoint24Q (endpointMeanCornerK 18 17 h) (endpointMeanCornerA 18 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 18 17, endpointRunWeightQ (endpointMeanCutoff 18 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 18 17) = (217475499/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 18 17 h = (logRoundedQ ((endpointMeanCutoff 18 17:ℚ)/200)).2+(217475499/500000000000000:ℚ)+((endpointMeanRuns 18 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 18 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 18 17) r*endpointJoint24Q (endpointMeanCornerK 18 17 h) (endpointMeanCornerA 18 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 18 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 18 17 h≤endpointMeanCorner 18 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 18 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint18_17

namespace EndpointAnalyticJoint18_18
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 1134 (.branch 1013 (.branch 952 (.leaf (75958795200000:ℤ)) (.leaf (4232433900000:ℤ))) (.branch 1070 (.leaf (3504183900000:ℤ)) (.leaf (3508622900000:ℤ)))) (.branch 1237 (.branch 1176 (.leaf (2017818000000:ℤ)) (.leaf (2686314100000:ℤ))) (.branch 1287 (.leaf (1938501400000:ℤ)) (.branch 1380 (.leaf (3224267300000:ℤ)) (.leaf (3044674900000:ℤ)))))) (.branch 1943 (.branch 1700 (.branch 1587 (.leaf (2200783400000:ℤ)) (.leaf (2002753900000:ℤ))) (.branch 1796 (.leaf (1325083900000:ℤ)) (.leaf (1593363200000:ℤ)))) (.branch 2573 (.branch 2116 (.leaf (1316278400000:ℤ)) (.leaf (2029919200000:ℤ))) (.branch 3283 (.leaf (927087200000:ℤ)) (.branch 4533 (.leaf (229207200000:ℤ)) (.leaf (20057900000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 145 (.branch 129 (.branch 121 (.leaf (1885931446230841:ℤ)) (.leaf (2016209679233336:ℤ))) (.branch 137 (.leaf (2129969963409057:ℤ)) (.leaf (2253214277680519:ℤ)))) (.branch 153 (.branch 149 (.leaf (2387008955121268:ℤ)) (.leaf (2458237001440896:ℤ))) (.branch 156 (.leaf (2532573170096852:ℤ)) (.branch 160 (.leaf (2590473212143111:ℤ)) (.leaf (2670691288997701:ℤ)))))) (.branch 181 (.branch 174 (.branch 169 (.leaf (2754546889881967:ℤ)) (.leaf (2864818278989889:ℤ))) (.branch 177 (.leaf (2981584917368117:ℤ)) (.leaf (3054973738774840:ℤ)))) (.branch 189 (.branch 184 (.leaf (3156955526884395:ℤ)) (.leaf (3236704864186513:ℤ))) (.branch 194 (.leaf (3376242696322935:ℤ)) (.branch 200 (.leaf (3524658155863052:ℤ)) (.leaf (3715548151378932:ℤ))))))), (.branch 164 (.branch 145 (.branch 129 (.branch 121 (.leaf (1894271172362645:ℤ)) (.leaf (2027016225110324:ℤ))) (.branch 137 (.leaf (2143158204949375:ℤ)) (.leaf (2269213273816742:ℤ)))) (.branch 153 (.branch 149 (.leaf (2406320789906674:ℤ)) (.leaf (2479420027321291:ℤ))) (.branch 156 (.leaf (2555786650606271:ℤ)) (.branch 160 (.leaf (2615322101621417:ℤ)) (.leaf (2697882487268779:ℤ)))))) (.branch 181 (.branch 174 (.branch 169 (.leaf (2784279789141866:ℤ)) (.leaf (2898035145573738:ℤ))) (.branch 177 (.leaf (3018661805130727:ℤ)) (.leaf (3094564430365745:ℤ)))) (.branch 189 (.branch 184 (.leaf (3200149291981197:ℤ)) (.leaf (3282803502441618:ℤ))) (.branch 194 (.leaf (3427603856798590:ℤ)) (.branch 200 (.leaf (3581861134528900:ℤ)) (.leaf (3780622905239869:ℤ))))))), (.branch 164 (.branch 145 (.branch 129 (.branch 121 (.leaf (1891642158629496:ℤ)) (.leaf (2023882189135767:ℤ))) (.branch 137 (.leaf (2139613231920490:ℤ)) (.leaf (2265268110964530:ℤ)))) (.branch 153 (.branch 149 (.leaf (2402008382745619:ℤ)) (.leaf (2474945503875736:ℤ))) (.branch 156 (.leaf (2551170494566248:ℤ)) (.branch 160 (.leaf (2610616482609541:ℤ)) (.leaf (2693085034239682:ℤ)))))) (.branch 181 (.branch 174 (.branch 169 (.leaf (2779428588534629:ℤ)) (.leaf (2893183291978850:ℤ))) (.branch 177 (.leaf (3013901587343625:ℤ)) (.leaf (3089913071758022:ℤ)))) (.branch 189 (.branch 184 (.leaf (3195718001578452:ℤ)) (.leaf (3278602112916188:ℤ))) (.branch 194 (.leaf (3423931909631090:ℤ)) (.branch 200 (.leaf (3578937566066811:ℤ)) (.leaf (3778956459408964:ℤ))))))), (.branch 164 (.branch 145 (.branch 129 (.branch 121 (.leaf (1900326311488818:ℤ)) (.leaf (2035159253207335:ℤ))) (.branch 137 (.leaf (2153401522681771:ℤ)) (.leaf (2282029008866250:ℤ)))) (.branch 153 (.branch 149 (.leaf (2422284392484724:ℤ)) (.leaf (2497212110062469:ℤ))) (.branch 156 (.leaf (2575601123965603:ℤ)) (.branch 160 (.leaf (2636793025185951:ℤ)) (.leaf (2721766541299755:ℤ)))))) (.branch 181 (.branch 174 (.branch 169 (.leaf (2810833943539751:ℤ)) (.leaf (2928331453741601:ℤ))) (.branch 177 (.leaf (3053208401699958:ℤ)) (.leaf (3131934612043734:ℤ)))) (.branch 189 (.branch 184 (.leaf (3241639145024743:ℤ)) (.leaf (3327674310051965:ℤ))) (.branch 194 (.leaf (3478728210762720:ℤ)) (.branch 200 (.leaf (3640110715411691:ℤ)) (.leaf (3848758250096147:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 18 18) 8000 (endpointMeanRuns 18 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 18 18, EndpointRunConditions (endpointMeanCutoff 18 18) (endpointMeanBox 18 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 18 18 h) (endpointMeanCornerA 18 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 18, endpointJoint24Q (endpointMeanCornerK 18 18 h) (endpointMeanCornerA 18 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 18 18, endpointRunWeightQ (endpointMeanCutoff 18 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 18 18) = (433640359/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 18 18 h = (logRoundedQ ((endpointMeanCutoff 18 18:ℚ)/200)).2+(433640359/1000000000000000:ℚ)+((endpointMeanRuns 18 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 18 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 18 18) r*endpointJoint24Q (endpointMeanCornerK 18 18 h) (endpointMeanCornerA 18 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 18 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 18 18 h≤endpointMeanCorner 18 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 18 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint18_18

namespace EndpointAnalyticJoint18_19
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 1134 (.branch 952 (.leaf (73183258600000:ℤ)) (.branch 1013 (.leaf (4202925200000:ℤ)) (.leaf (7449122300000:ℤ)))) (.branch 1237 (.leaf (4919759200000:ℤ)) (.branch 1380 (.leaf (5460825100000:ℤ)) (.leaf (3027466000000:ℤ))))) (.branch 2116 (.branch 1700 (.leaf (4543672500000:ℤ)) (.branch 1943 (.leaf (3154902100000:ℤ)) (.leaf (1309939200000:ℤ)))) (.branch 2573 (.leaf (2020631300000:ℤ)) (.branch 3283 (.leaf (923168400000:ℤ)) (.leaf (581460600000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 145 (.branch 129 (.leaf (1894271172362645:ℤ)) (.branch 137 (.leaf (2143158204949375:ℤ)) (.leaf (2269213273816742:ℤ)))) (.branch 149 (.leaf (2406320789906674:ℤ)) (.branch 156 (.leaf (2479420027321291:ℤ)) (.leaf (2615322101621417:ℤ))))) (.branch 184 (.branch 169 (.leaf (2784279789141866:ℤ)) (.branch 177 (.leaf (2898035145573738:ℤ)) (.leaf (3094564430365745:ℤ)))) (.branch 194 (.leaf (3282803502441618:ℤ)) (.branch 200 (.leaf (3581861134528900:ℤ)) (.leaf (3780622905239869:ℤ)))))), (.branch 164 (.branch 145 (.branch 129 (.leaf (1902647777370454:ℤ)) (.branch 137 (.leaf (2156428104784369:ℤ)) (.leaf (2285325871166974:ℤ)))) (.branch 149 (.leaf (2425788864978477:ℤ)) (.branch 156 (.leaf (2500785590762213:ℤ)) (.leaf (2640409351915584:ℤ))))) (.branch 184 (.branch 169 (.leaf (2814333628771901:ℤ)) (.branch 177 (.leaf (2931637153593512:ℤ)) (.leaf (3134668194406583:ℤ)))) (.branch 194 (.leaf (3329558698689538:ℤ)) (.branch 200 (.leaf (3639992481457295:ℤ)) (.leaf (3846837389610961:ℤ)))))), (.branch 164 (.branch 145 (.branch 129 (.leaf (1900326311488818:ℤ)) (.branch 137 (.leaf (2153401522681771:ℤ)) (.leaf (2282029008866250:ℤ)))) (.branch 149 (.leaf (2422284392484724:ℤ)) (.branch 156 (.leaf (2497212110062469:ℤ)) (.leaf (2636793025185951:ℤ))))) (.branch 184 (.branch 169 (.leaf (2810833943539751:ℤ)) (.branch 177 (.leaf (2928331453741601:ℤ)) (.leaf (3131934612043734:ℤ)))) (.branch 194 (.leaf (3327674310051965:ℤ)) (.branch 200 (.leaf (3640110715411691:ℤ)) (.leaf (3848758250096147:ℤ)))))), (.branch 164 (.branch 145 (.branch 129 (.leaf (1909050331566440:ℤ)) (.branch 137 (.leaf (2167278669204121:ℤ)) (.leaf (2298913921977074:ℤ)))) (.branch 149 (.leaf (2442731557567788:ℤ)) (.branch 156 (.leaf (2519679044599983:ℤ)) (.leaf (2663232038862891:ℤ))))) (.branch 184 (.branch 169 (.leaf (2842594154333245:ℤ)) (.branch 177 (.leaf (2963906616890242:ℤ)) (.leaf (3174527627903991:ℤ)))) (.branch 194 (.leaf (3377480991107658:ℤ)) (.branch 200 (.leaf (3702329469529404:ℤ)) (.leaf (3919849362328968:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 18 19) 8000 (endpointMeanRuns 18 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 18 19, EndpointRunConditions (endpointMeanCutoff 18 19) (endpointMeanBox 18 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 18 19 h) (endpointMeanCornerA 18 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 18 19, endpointJoint24Q (endpointMeanCornerK 18 19 h) (endpointMeanCornerA 18 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 18 19, endpointRunWeightQ (endpointMeanCutoff 18 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 18 19) = (432344473/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 18 19 h = (logRoundedQ ((endpointMeanCutoff 18 19:ℚ)/200)).2+(432344473/1000000000000000:ℚ)+((endpointMeanRuns 18 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 18 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 18 19) r*endpointJoint24Q (endpointMeanCornerK 18 19 h) (endpointMeanCornerA 18 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 18 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 18 19 h≤endpointMeanCorner 18 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 18 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint18_19

namespace EndpointAnalyticJoint19_04
private noncomputable def weights : IntegerLookupTree := (.branch 1308 (.branch 929 (.leaf (121791288500000:ℤ)) (.leaf (33031011800000:ℤ))) (.branch 1934 (.leaf (21318546800000:ℤ)) (.leaf (22083600600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 171 (.branch 148 (.leaf (1779311424115040:ℤ)) (.leaf (2183347698619376:ℤ))) (.branch 200 (.leaf (2490720732128720:ℤ)) (.leaf (2958907066480733:ℤ)))), (.branch 171 (.branch 148 (.leaf (1782294318756147:ℤ)) (.leaf (2190398839829512:ℤ))) (.branch 200 (.leaf (2502062192455745:ℤ)) (.leaf (2978778467575754:ℤ)))), (.branch 171 (.branch 148 (.leaf (1780742576536024:ℤ)) (.leaf (2187265129863232:ℤ))) (.branch 200 (.leaf (2497669909999500:ℤ)) (.leaf (2972817444117638:ℤ)))), (.branch 171 (.branch 148 (.leaf (1783841044368466:ℤ)) (.leaf (2194639354411061:ℤ))) (.branch 200 (.leaf (2509594714493223:ℤ)) (.leaf (2993890135037748:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 19 4) 8000 (endpointMeanRuns 19 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 19 4, EndpointRunConditions (endpointMeanCutoff 19 4) (endpointMeanBox 19 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 19 4 h) (endpointMeanCornerA 19 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 4, endpointJoint24Q (endpointMeanCornerK 19 4 h) (endpointMeanCornerA 19 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 19 4, endpointRunWeightQ (endpointMeanCutoff 19 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 19 4) = (452476823/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 19 4 h = (logRoundedQ ((endpointMeanCutoff 19 4:ℚ)/200)).2+(452476823/1000000000000000:ℚ)+((endpointMeanRuns 19 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 19 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 19 4) r*endpointJoint24Q (endpointMeanCornerK 19 4 h) (endpointMeanCornerA 19 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 19 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 19 4 h≤endpointMeanCorner 19 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 19 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint19_04

namespace EndpointAnalyticJoint19_05
private noncomputable def weights : IntegerLookupTree := (.branch 1308 (.branch 929 (.leaf (118864367000000:ℤ)) (.leaf (32873874800000:ℤ))) (.branch 1934 (.leaf (21232964800000:ℤ)) (.leaf (22008948300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 171 (.branch 148 (.leaf (1782294318756147:ℤ)) (.leaf (2190398839829512:ℤ))) (.branch 200 (.leaf (2502062192455745:ℤ)) (.leaf (2978778467575754:ℤ)))), (.branch 171 (.branch 148 (.leaf (1790476477434400:ℤ)) (.leaf (2209796378961893:ℤ))) (.branch 200 (.leaf (2533339322076347:ℤ)) (.leaf (3033800025333983:ℤ)))), (.branch 171 (.branch 148 (.leaf (1783841044368466:ℤ)) (.leaf (2194639354411061:ℤ))) (.branch 200 (.leaf (2509594714493223:ℤ)) (.leaf (2993890135037748:ℤ)))), (.branch 171 (.branch 148 (.leaf (1792341230797828:ℤ)) (.leaf (2214931053130876:ℤ))) (.branch 200 (.leaf (2542494094266713:ℤ)) (.leaf (3052278339568213:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 19 5) 8000 (endpointMeanRuns 19 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 19 5, EndpointRunConditions (endpointMeanCutoff 19 5) (endpointMeanBox 19 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 19 5 h) (endpointMeanCornerA 19 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 5, endpointJoint24Q (endpointMeanCornerK 19 5 h) (endpointMeanCornerA 19 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 19 5, endpointRunWeightQ (endpointMeanCutoff 19 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 19 5) = (90291617/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 19 5 h = (logRoundedQ ((endpointMeanCutoff 19 5:ℚ)/200)).2+(90291617/200000000000000:ℚ)+((endpointMeanRuns 19 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 19 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 19 5) r*endpointJoint24Q (endpointMeanCornerK 19 5 h) (endpointMeanCornerA 19 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 19 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 19 5 h≤endpointMeanCorner 19 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 19 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint19_05

namespace EndpointAnalyticJoint19_06
private noncomputable def weights : IntegerLookupTree := (.branch 1308 (.branch 929 (.leaf (113902286400000:ℤ)) (.leaf (32602187400000:ℤ))) (.branch 1934 (.leaf (21084994800000:ℤ)) (.leaf (21879875600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 171 (.branch 148 (.leaf (1790476477434400:ℤ)) (.leaf (2209796378961893:ℤ))) (.branch 200 (.leaf (2533339322076347:ℤ)) (.leaf (3033800025333983:ℤ)))), (.branch 171 (.branch 148 (.leaf (1798696198775526:ℤ)) (.leaf (2229365697095222:ℤ))) (.branch 200 (.leaf (2565007432720624:ℤ)) (.leaf (3089837896272630:ℤ)))), (.branch 171 (.branch 148 (.leaf (1792341230797828:ℤ)) (.leaf (2214931053130876:ℤ))) (.branch 200 (.leaf (2542494094266713:ℤ)) (.leaf (3052278339568213:ℤ)))), (.branch 171 (.branch 148 (.leaf (1800881921491604:ℤ)) (.leaf (2235410369481857:ℤ))) (.branch 200 (.leaf (2575824766464924:ℤ)) (.leaf (3111805257369542:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 19 6) 8000 (endpointMeanRuns 19 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 19 6, EndpointRunConditions (endpointMeanCutoff 19 6) (endpointMeanBox 19 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 19 6 h) (endpointMeanCornerA 19 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 6, endpointJoint24Q (endpointMeanCornerK 19 6 h) (endpointMeanCornerA 19 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 19 6, endpointRunWeightQ (endpointMeanCutoff 19 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 19 6) = (7026511/15625000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 19 6 h = (logRoundedQ ((endpointMeanCutoff 19 6:ℚ)/200)).2+(7026511/15625000000000:ℚ)+((endpointMeanRuns 19 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 19 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 19 6) r*endpointJoint24Q (endpointMeanCornerK 19 6 h) (endpointMeanCornerA 19 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 19 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 19 6 h≤endpointMeanCorner 19 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 19 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint19_06

namespace EndpointAnalyticJoint19_07
private noncomputable def weights : IntegerLookupTree := (.branch 1308 (.branch 929 (.leaf (109805652800000:ℤ)) (.leaf (32372576000000:ℤ))) (.branch 1934 (.leaf (20959940800000:ℤ)) (.branch 3201 (.leaf (7634926800000:ℤ)) (.leaf (758824600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 148 (.branch 129 (.leaf (1798696198775526:ℤ)) (.leaf (1993646370198620:ℤ))) (.branch 171 (.leaf (2229365697095222:ℤ)) (.branch 200 (.leaf (2565007432720624:ℤ)) (.leaf (3089837896272630:ℤ))))), (.branch 148 (.branch 129 (.leaf (1806953655222234:ℤ)) (.leaf (2006494007994726:ℤ))) (.branch 171 (.leaf (2249108315454696:ℤ)) (.branch 200 (.leaf (2597071411862677:ℤ)) (.leaf (3146910852896927:ℤ))))), (.branch 148 (.branch 129 (.leaf (1800881921491604:ℤ)) (.leaf (1997291491262132:ℤ))) (.branch 171 (.leaf (2235410369481857:ℤ)) (.branch 200 (.leaf (2575824766464924:ℤ)) (.leaf (3111805257369542:ℤ))))), (.branch 148 (.branch 129 (.leaf (1809463309456789:ℤ)) (.leaf (2010687253877682:ℤ))) (.branch 171 (.leaf (2256079038182027:ℤ)) (.branch 200 (.leaf (2609592385089749:ℤ)) (.leaf (3172493096144883:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 19 7) 8000 (endpointMeanRuns 19 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 19 7, EndpointRunConditions (endpointMeanCutoff 19 7) (endpointMeanBox 19 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 19 7 h) (endpointMeanCornerA 19 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 7, endpointJoint24Q (endpointMeanCornerK 19 7 h) (endpointMeanCornerA 19 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 19 7, endpointRunWeightQ (endpointMeanCutoff 19 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 19 7) = (224104053/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 19 7 h = (logRoundedQ ((endpointMeanCutoff 19 7:ℚ)/200)).2+(224104053/500000000000000:ℚ)+((endpointMeanRuns 19 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 19 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 19 7) r*endpointJoint24Q (endpointMeanCornerK 19 7 h) (endpointMeanCornerA 19 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 19 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 19 7 h≤endpointMeanCorner 19 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 19 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint19_07

namespace EndpointAnalyticJoint19_08
private noncomputable def weights : IntegerLookupTree := (.branch 1308 (.branch 929 (.leaf (105848067400000:ℤ)) (.leaf (32145895900000:ℤ))) (.branch 1934 (.leaf (20836483400000:ℤ)) (.branch 3201 (.leaf (7596751700000:ℤ)) (.leaf (755623900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 148 (.branch 129 (.leaf (1806953655222234:ℤ)) (.leaf (2006494007994726:ℤ))) (.branch 171 (.leaf (2249108315454696:ℤ)) (.branch 200 (.leaf (2597071411862677:ℤ)) (.leaf (3146910852896927:ℤ))))), (.branch 148 (.branch 129 (.leaf (1815249020008897:ℤ)) (.leaf (2019424439710255:ℤ))) (.branch 171 (.leaf (2269025768737034:ℤ)) (.branch 200 (.leaf (2629536208072665:ℤ)) (.leaf (3205038014462448:ℤ))))), (.branch 148 (.branch 129 (.leaf (1809463309456789:ℤ)) (.leaf (2010687253877682:ℤ))) (.branch 171 (.leaf (2256079038182027:ℤ)) (.branch 200 (.leaf (2609592385089749:ℤ)) (.leaf (3172493096144883:ℤ))))), (.branch 148 (.branch 129 (.leaf (1818085588620076:ℤ)) (.leaf (2024172861394110:ℤ))) (.branch 171 (.leaf (2276938809988664:ℤ)) (.branch 200 (.leaf (2643802678263887:ℤ)) (.leaf (3234364496702088:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 19 8) 8000 (endpointMeanRuns 19 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 19 8, EndpointRunConditions (endpointMeanCutoff 19 8) (endpointMeanBox 19 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 19 8 h) (endpointMeanCornerA 19 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 8, endpointJoint24Q (endpointMeanCornerK 19 8 h) (endpointMeanCornerA 19 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 19 8, endpointRunWeightQ (endpointMeanCutoff 19 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 19 8) = (446738513/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 19 8 h = (logRoundedQ ((endpointMeanCutoff 19 8:ℚ)/200)).2+(446738513/1000000000000000:ℚ)+((endpointMeanRuns 19 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 19 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 19 8) r*endpointJoint24Q (endpointMeanCornerK 19 8 h) (endpointMeanCornerA 19 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 19 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 19 8 h≤endpointMeanCorner 19 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 19 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint19_08

namespace EndpointAnalyticJoint19_09
private noncomputable def weights : IntegerLookupTree := (.branch 1308 (.branch 929 (.leaf (102024550600000:ℤ)) (.branch 1080 (.leaf (12540469800000:ℤ)) (.leaf (13702176100000:ℤ)))) (.branch 1934 (.leaf (20714582100000:ℤ)) (.branch 3201 (.leaf (7559057800000:ℤ)) (.leaf (752463700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 171 (.branch 129 (.leaf (1815249020008897:ℤ)) (.branch 148 (.leaf (2019424439710255:ℤ)) (.leaf (2269025768737034:ℤ)))) (.branch 186 (.leaf (2629536208072665:ℤ)) (.branch 200 (.leaf (2907605979343408:ℤ)) (.leaf (3205038014462448:ℤ))))), (.branch 171 (.branch 129 (.leaf (1823582467165156:ℤ)) (.branch 148 (.leaf (2032438198893340:ℤ)) (.leaf (2289119605229789:ℤ)))) (.branch 186 (.leaf (2662406831780559:ℤ)) (.branch 200 (.leaf (2952313056567864:ℤ)) (.leaf (3264238853380015:ℤ))))), (.branch 171 (.branch 129 (.leaf (1818085588620076:ℤ)) (.branch 148 (.leaf (2024172861394110:ℤ)) (.leaf (2276938809988664:ℤ)))) (.branch 186 (.leaf (2643802678263887:ℤ)) (.branch 200 (.leaf (2928351623486901:ℤ)) (.leaf (3234364496702088:ℤ))))), (.branch 171 (.branch 129 (.leaf (1826748953832236:ℤ)) (.branch 148 (.leaf (2037748916397945:ℤ)) (.leaf (2297991451846598:ℤ)))) (.branch 186 (.leaf (2678461449202496:ℤ)) (.branch 200 (.leaf (2975727455863798:ℤ)) (.leaf (3297442541400315:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 19 9) 8000 (endpointMeanRuns 19 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 19 9, EndpointRunConditions (endpointMeanCutoff 19 9) (endpointMeanBox 19 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 19 9 h) (endpointMeanCornerA 19 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 9, endpointJoint24Q (endpointMeanCornerK 19 9 h) (endpointMeanCornerA 19 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 19 9, endpointRunWeightQ (endpointMeanCutoff 19 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 19 9) = (111321861/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 19 9 h = (logRoundedQ ((endpointMeanCutoff 19 9:ℚ)/200)).2+(111321861/250000000000000:ℚ)+((endpointMeanRuns 19 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 19 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 19 9) r*endpointJoint24Q (endpointMeanCornerK 19 9 h) (endpointMeanCornerA 19 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 19 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 19 9 h≤endpointMeanCorner 19 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 19 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint19_09

namespace EndpointAnalyticJoint19_10
private noncomputable def weights : IntegerLookupTree := (.branch 1308 (.branch 929 (.leaf (98330321400000:ℤ)) (.branch 1080 (.leaf (12450228700000:ℤ)) (.leaf (13612197800000:ℤ)))) (.branch 1934 (.leaf (20594198300000:ℤ)) (.branch 3201 (.leaf (7521833200000:ℤ)) (.leaf (749342700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 171 (.branch 129 (.leaf (1823582467165156:ℤ)) (.branch 148 (.leaf (2032438198893340:ℤ)) (.leaf (2289119605229789:ℤ)))) (.branch 186 (.leaf (2662406831780559:ℤ)) (.branch 200 (.leaf (2952313056567864:ℤ)) (.leaf (3264238853380015:ℤ))))), (.branch 171 (.branch 129 (.leaf (1831954171519593:ℤ)) (.branch 148 (.leaf (2045535822530449:ℤ)) (.leaf (2309391386931697:ℤ)))) (.branch 186 (.leaf (2695688356049405:ℤ)) (.branch 200 (.leaf (2997707545624652:ℤ)) (.leaf (3324533201738885:ℤ))))), (.branch 171 (.branch 129 (.leaf (1826748953832236:ℤ)) (.branch 148 (.leaf (2037748916397945:ℤ)) (.leaf (2297991451846598:ℤ)))) (.branch 186 (.leaf (2678461449202496:ℤ)) (.branch 200 (.leaf (2975727455863798:ℤ)) (.leaf (3297442541400315:ℤ))))), (.branch 171 (.branch 129 (.leaf (1835453600872531:ℤ)) (.branch 148 (.leaf (2051416025517264:ℤ)) (.leaf (2319238747037885:ℤ)))) (.branch 186 (.leaf (2713574577197652:ℤ)) (.branch 200 (.leaf (3023869749985043:ℤ)) (.leaf (3361750762761384:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 19 10) 8000 (endpointMeanRuns 19 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 19 10, EndpointRunConditions (endpointMeanCutoff 19 10) (endpointMeanBox 19 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 19 10 h) (endpointMeanCornerA 19 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 10, endpointJoint24Q (endpointMeanCornerK 19 10 h) (endpointMeanCornerA 19 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 19 10, endpointRunWeightQ (endpointMeanCutoff 19 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 19 10) = (221927219/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 19 10 h = (logRoundedQ ((endpointMeanCutoff 19 10:ℚ)/200)).2+(221927219/500000000000000:ℚ)+((endpointMeanRuns 19 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 19 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 19 10) r*endpointJoint24Q (endpointMeanCornerK 19 10 h) (endpointMeanCornerA 19 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 19 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 19 10 h≤endpointMeanCorner 19 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 19 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint19_10

namespace EndpointAnalyticJoint19_11
private noncomputable def weights : IntegerLookupTree := (.branch 1308 (.branch 929 (.leaf (94760788100000:ℤ)) (.branch 1080 (.leaf (12361097100000:ℤ)) (.leaf (13523325900000:ℤ)))) (.branch 1934 (.branch 1522 (.leaf (7619322900000:ℤ)) (.leaf (8463175000000:ℤ))) (.branch 3201 (.leaf (7485066200000:ℤ)) (.leaf (746260200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 129 (.leaf (1831954171519593:ℤ)) (.branch 148 (.leaf (2045535822530449:ℤ)) (.leaf (2309391386931697:ℤ)))) (.branch 186 (.branch 171 (.leaf (2517510376235314:ℤ)) (.leaf (2695688356049405:ℤ))) (.branch 200 (.leaf (2997707545624652:ℤ)) (.leaf (3324533201738885:ℤ))))), (.branch 161 (.branch 129 (.leaf (1840364308703404:ℤ)) (.branch 148 (.leaf (2058717851068545:ℤ)) (.leaf (2329842689674112:ℤ)))) (.branch 186 (.branch 171 (.leaf (2544724335188197:ℤ)) (.leaf (2729385917358287:ℤ))) (.branch 200 (.leaf (3043800016093725:ℤ)) (.leaf (3385941257950426:ℤ))))), (.branch 161 (.branch 129 (.leaf (1835453600872531:ℤ)) (.branch 148 (.leaf (2051416025517264:ℤ)) (.leaf (2319238747037885:ℤ)))) (.branch 186 (.branch 171 (.leaf (2531345791454245:ℤ)) (.leaf (2713574577197652:ℤ))) (.branch 200 (.leaf (3023869749985043:ℤ)) (.leaf (3361750762761384:ℤ))))), (.branch 161 (.branch 129 (.leaf (1844199726453122:ℤ)) (.branch 148 (.leaf (2065174799448753:ℤ)) (.leaf (2340682495332849:ℤ)))) (.branch 186 (.branch 171 (.leaf (2559984475491093:ℤ)) (.leaf (2749148018615639:ℤ))) (.branch 200 (.leaf (3072790905919960:ℤ)) (.leaf (3427313152249024:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 19 11) 8000 (endpointMeanRuns 19 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 19 11, EndpointRunConditions (endpointMeanCutoff 19 11) (endpointMeanBox 19 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 19 11 h) (endpointMeanCornerA 19 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 11, endpointJoint24Q (endpointMeanCornerK 19 11 h) (endpointMeanCornerA 19 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 19 11, endpointRunWeightQ (endpointMeanCutoff 19 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 19 11) = (442439053/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 19 11 h = (logRoundedQ ((endpointMeanCutoff 19 11:ℚ)/200)).2+(442439053/1000000000000000:ℚ)+((endpointMeanRuns 19 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 19 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 19 11) r*endpointJoint24Q (endpointMeanCornerK 19 11 h) (endpointMeanCornerA 19 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 19 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 19 11 h≤endpointMeanCorner 19 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 19 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint19_11

namespace EndpointAnalyticJoint19_12
private noncomputable def weights : IntegerLookupTree := (.branch 1308 (.branch 1080 (.branch 929 (.leaf (90748059300000:ℤ)) (.leaf (12258476800000:ℤ))) (.branch 1161 (.leaf (4776530700000:ℤ)) (.leaf (7279311900000:ℤ)))) (.branch 1934 (.branch 1522 (.leaf (7566606700000:ℤ)) (.leaf (8409351400000:ℤ))) (.branch 2264 (.leaf (2594742900000:ℤ)) (.branch 3201 (.leaf (2614933600000:ℤ)) (.leaf (742711100000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 141 (.branch 129 (.leaf (1840364308703404:ℤ)) (.leaf (2058717851068545:ℤ))) (.branch 148 (.leaf (2224503567961636:ℤ)) (.leaf (2329842689674112:ℤ)))) (.branch 180 (.branch 171 (.leaf (2544724335188197:ℤ)) (.leaf (2729385917358287:ℤ))) (.branch 186 (.leaf (2912163877662974:ℤ)) (.branch 200 (.leaf (3043800016093725:ℤ)) (.leaf (3385941257950426:ℤ)))))), (.branch 161 (.branch 141 (.branch 129 (.leaf (1848813055154049:ℤ)) (.leaf (2071984828437385:ℤ))) (.branch 148 (.leaf (2242097002568106:ℤ)) (.leaf (2350475103243488:ℤ)))) (.branch 180 (.branch 171 (.leaf (2572232473489408:ℤ)) (.leaf (2763504716395043:ℤ))) (.branch 186 (.leaf (2953441515689657:ℤ)) (.branch 200 (.leaf (3090601200071904:ℤ)) (.leaf (3448483593514549:ℤ)))))), (.branch 161 (.branch 141 (.branch 129 (.leaf (1844199726453122:ℤ)) (.leaf (2065174799448753:ℤ))) (.branch 148 (.leaf (2233486421880323:ℤ)) (.leaf (2340682495332849:ℤ)))) (.branch 180 (.branch 171 (.leaf (2559984475491093:ℤ)) (.leaf (2749148018615639:ℤ))) (.branch 186 (.leaf (2937046254267586:ℤ)) (.branch 200 (.leaf (3072790905919960:ℤ)) (.leaf (3427313152249024:ℤ)))))), (.branch 161 (.branch 141 (.branch 129 (.leaf (1852987528223535:ℤ)) (.leaf (2079025852985038:ℤ))) (.branch 148 (.leaf (2251907041055667:ℤ)) (.leaf (2362324513142554:ℤ)))) (.branch 180 (.branch 171 (.leaf (2588947166712632:ℤ)) (.leaf (2785187807907364:ℤ))) (.branch 186 (.leaf (2980789209872712:ℤ)) (.branch 200 (.leaf (3122503524350248:ℤ)) (.leaf (3494154169219382:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 19 12) 8000 (endpointMeanRuns 19 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 19 12, EndpointRunConditions (endpointMeanCutoff 19 12) (endpointMeanBox 19 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 19 12 h) (endpointMeanCornerA 19 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 12, endpointJoint24Q (endpointMeanCornerK 19 12 h) (endpointMeanCornerA 19 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 19 12, endpointRunWeightQ (endpointMeanCutoff 19 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 19 12) = (110202367/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 19 12 h = (logRoundedQ ((endpointMeanCutoff 19 12:ℚ)/200)).2+(110202367/250000000000000:ℚ)+((endpointMeanRuns 19 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 19 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 19 12) r*endpointJoint24Q (endpointMeanCornerK 19 12 h) (endpointMeanCornerA 19 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 19 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 19 12 h≤endpointMeanCorner 19 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 19 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint19_12

namespace EndpointAnalyticJoint19_13
private noncomputable def weights : IntegerLookupTree := (.branch 1386 (.branch 1080 (.branch 929 (.leaf (87433797500000:ℤ)) (.branch 988 (.leaf (4670906300000:ℤ)) (.leaf (6516546000000:ℤ)))) (.branch 1161 (.leaf (4744885400000:ℤ)) (.branch 1308 (.leaf (7233434200000:ℤ)) (.leaf (2813514400000:ℤ))))) (.branch 1934 (.branch 1522 (.leaf (4080065100000:ℤ)) (.branch 1658 (.leaf (3002558300000:ℤ)) (.leaf (4242452700000:ℤ)))) (.branch 2264 (.leaf (2581913200000:ℤ)) (.branch 3201 (.leaf (2602979600000:ℤ)) (.leaf (739708500000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 167 (.branch 148 (.branch 129 (.leaf (1848813055154049:ℤ)) (.branch 141 (.leaf (2071984828437385:ℤ)) (.leaf (2242097002568106:ℤ)))) (.branch 156 (.leaf (2350475103243488:ℤ)) (.branch 161 (.leaf (2483580538124375:ℤ)) (.leaf (2572232473489408:ℤ))))) (.branch 186 (.branch 171 (.leaf (2684647592978175:ℤ)) (.branch 180 (.leaf (2763504716395043:ℤ)) (.leaf (2953441515689657:ℤ)))) (.branch 194 (.leaf (3090601200071904:ℤ)) (.branch 200 (.leaf (3288151113189327:ℤ)) (.leaf (3448483593514549:ℤ)))))), (.branch 167 (.branch 148 (.branch 129 (.leaf (1857300588119004:ℤ)) (.branch 141 (.leaf (2085337302071980:ℤ)) (.leaf (2259829582350918:ℤ)))) (.branch 156 (.leaf (2371290231504965:ℤ)) (.branch 161 (.leaf (2508483296584386:ℤ)) (.leaf (2600037971179350:ℤ))))) (.branch 186 (.branch 171 (.leaf (2716336353713906:ℤ)) (.branch 180 (.leaf (2798050018858929:ℤ)) (.leaf (2995304231848156:ℤ)))) (.branch 194 (.leaf (3138121994671729:ℤ)) (.branch 200 (.leaf (3344353982169999:ℤ)) (.leaf (3512181159911048:ℤ)))))), (.branch 167 (.branch 148 (.branch 129 (.leaf (1852987528223535:ℤ)) (.branch 141 (.leaf (2079025852985038:ℤ)) (.leaf (2251907041055667:ℤ)))) (.branch 156 (.leaf (2362324513142554:ℤ)) (.branch 161 (.leaf (2498236838253071:ℤ)) (.leaf (2588947166712632:ℤ))))) (.branch 186 (.branch 171 (.leaf (2704194055262195:ℤ)) (.branch 180 (.leaf (2785187807907364:ℤ)) (.leaf (2980789209872712:ℤ)))) (.branch 194 (.leaf (3122503524350248:ℤ)) (.branch 200 (.leaf (3327312402591346:ℤ)) (.leaf (3494154169219382:ℤ)))))), (.branch 167 (.branch 148 (.branch 129 (.leaf (1861817204775098:ℤ)) (.branch 141 (.leaf (2092969805042118:ℤ)) (.leaf (2270479583792076:ℤ)))) (.branch 156 (.leaf (2384166633672642:ℤ)) (.branch 161 (.leaf (2524428878828547:ℤ)) (.leaf (2618237530812978:ℤ))))) (.branch 186 (.branch 171 (.leaf (2737640809169244:ℤ)) (.branch 180 (.leaf (2821700058632018:ℤ)) (.leaf (3025183652039304:ℤ)))) (.branch 194 (.leaf (3173020409815571:ℤ)) (.branch 200 (.leaf (3387268111340124:ℤ)) (.leaf (3562298750046089:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 19 13) 8000 (endpointMeanRuns 19 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 19 13, EndpointRunConditions (endpointMeanCutoff 19 13) (endpointMeanBox 19 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 19 13 h) (endpointMeanCornerA 19 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 13, endpointJoint24Q (endpointMeanCornerK 19 13 h) (endpointMeanCornerA 19 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 19 13, endpointRunWeightQ (endpointMeanCutoff 19 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 19 13) = (439430809/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 19 13 h = (logRoundedQ ((endpointMeanCutoff 19 13:ℚ)/200)).2+(439430809/1000000000000000:ℚ)+((endpointMeanRuns 19 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 19 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 19 13) r*endpointJoint24Q (endpointMeanCornerK 19 13 h) (endpointMeanCornerA 19 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 19 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 19 13 h≤endpointMeanCorner 19 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 19 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint19_13

namespace EndpointAnalyticJoint19_14
private noncomputable def weights : IntegerLookupTree := (.branch 1386 (.branch 1080 (.branch 988 (.branch 929 (.leaf (84230843800000:ℤ)) (.leaf (4637205400000:ℤ))) (.branch 1032 (.leaf (3072362000000:ℤ)) (.leaf (3073482500000:ℤ)))) (.branch 1222 (.branch 1161 (.leaf (4713614700000:ℤ)) (.leaf (2999427900000:ℤ))) (.branch 1308 (.leaf (3708027000000:ℤ)) (.leaf (2796703500000:ℤ))))) (.branch 1934 (.branch 1658 (.branch 1522 (.leaf (4056559500000:ℤ)) (.leaf (2985986500000:ℤ))) (.branch 1785 (.leaf (2053739600000:ℤ)) (.leaf (1782046500000:ℤ)))) (.branch 2509 (.branch 2264 (.leaf (2569235400000:ℤ)) (.leaf (904658300000:ℤ))) (.branch 3201 (.leaf (1137964100000:ℤ)) (.branch 4420 (.leaf (294532000000:ℤ)) (.leaf (27563400000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 141 (.branch 129 (.branch 121 (.leaf (1857300588119004:ℤ)) (.leaf (1979395355706835:ℤ))) (.branch 137 (.leaf (2085337302071980:ℤ)) (.leaf (2199446554328085:ℤ)))) (.branch 152 (.branch 148 (.leaf (2259829582350918:ℤ)) (.leaf (2371290231504965:ℤ))) (.branch 156 (.leaf (2438514315072017:ℤ)) (.leaf (2508483296584386:ℤ))))) (.branch 180 (.branch 171 (.branch 167 (.leaf (2600037971179350:ℤ)) (.leaf (2716336353713906:ℤ))) (.branch 176 (.leaf (2798050018858929:ℤ)) (.leaf (2905244156598211:ℤ)))) (.branch 190 (.branch 186 (.leaf (2995304231848156:ℤ)) (.leaf (3138121994671729:ℤ))) (.branch 194 (.leaf (3238862245761348:ℤ)) (.branch 200 (.leaf (3344353982169999:ℤ)) (.leaf (3512181159911048:ℤ))))))), (.branch 161 (.branch 141 (.branch 129 (.branch 121 (.leaf (1865827085659437:ℤ)) (.leaf (1990424539307095:ℤ))) (.branch 137 (.leaf (2098775822935164:ℤ)) (.leaf (2215720433326755:ℤ)))) (.branch 152 (.branch 148 (.leaf (2277702407799018:ℤ)) (.leaf (2392289692527066:ℤ))) (.branch 156 (.leaf (2461507316970920:ℤ)) (.leaf (2533635753964729:ℤ))))) (.branch 180 (.branch 171 (.branch 167 (.leaf (2628144042674240:ℤ)) (.leaf (2748399158908805:ℤ))) (.branch 176 (.leaf (2833027156273281:ℤ)) (.leaf (2944208756930963:ℤ)))) (.branch 190 (.branch 186 (.leaf (3037760319161911:ℤ)) (.leaf (3186373464558732:ℤ))) (.branch 194 (.leaf (3291388140345707:ℤ)) (.branch 200 (.leaf (3401517501185571:ℤ)) (.leaf (3577055295618326:ℤ))))))), (.branch 161 (.branch 141 (.branch 129 (.branch 121 (.leaf (1861817204775098:ℤ)) (.leaf (1985466444960519:ℤ))) (.branch 137 (.leaf (2092969805042118:ℤ)) (.leaf (2208988505419661:ℤ)))) (.branch 152 (.branch 148 (.leaf (2270479583792076:ℤ)) (.leaf (2384166633672642:ℤ))) (.branch 156 (.leaf (2452848792036204:ℤ)) (.leaf (2524428878828547:ℤ))))) (.branch 180 (.branch 171 (.branch 167 (.leaf (2618237530812978:ℤ)) (.leaf (2737640809169244:ℤ))) (.branch 176 (.leaf (2821700058632018:ℤ)) (.leaf (2932179178029470:ℤ)))) (.branch 190 (.branch 186 (.leaf (3025183652039304:ℤ)) (.leaf (3173020409815571:ℤ))) (.branch 194 (.leaf (3277561900403365:ℤ)) (.branch 200 (.leaf (3387268111340124:ℤ)) (.leaf (3562298750046089:ℤ))))))), (.branch 161 (.branch 141 (.branch 129 (.branch 121 (.leaf (1870688955645474:ℤ)) (.leaf (1996966237997467:ℤ))) (.branch 137 (.leaf (2107007278687061:ℤ)) (.leaf (2226021190601358:ℤ)))) (.branch 152 (.branch 148 (.leaf (2289205303075030:ℤ)) (.leaf (2406210707078636:ℤ))) (.branch 156 (.leaf (2477013749635564:ℤ)) (.leaf (2550895522267536:ℤ))))) (.branch 180 (.branch 171 (.branch 167 (.leaf (2647859274958527:ℤ)) (.leaf (2771501248382912:ℤ))) (.branch 176 (.leaf (2858690964494104:ℤ)) (.leaf (2973464415490774:ℤ)))) (.branch 190 (.branch 186 (.leaf (3070239283695166:ℤ)) (.leaf (3224354574011635:ℤ))) (.branch 194 (.leaf (3333542407422717:ℤ)) (.branch 200 (.leaf (3448304177619735:ℤ)) (.leaf (3631772317423226:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 19 14) 8000 (endpointMeanRuns 19 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 19 14, EndpointRunConditions (endpointMeanCutoff 19 14) (endpointMeanBox 19 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 19 14 h) (endpointMeanCornerA 19 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 14, endpointJoint24Q (endpointMeanCornerK 19 14 h) (endpointMeanCornerA 19 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 19 14, endpointRunWeightQ (endpointMeanCutoff 19 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 19 14) = (219034233/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 19 14 h = (logRoundedQ ((endpointMeanCutoff 19 14:ℚ)/200)).2+(219034233/500000000000000:ℚ)+((endpointMeanRuns 19 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 19 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 19 14) r*endpointJoint24Q (endpointMeanCornerK 19 14 h) (endpointMeanCornerA 19 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 19 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 19 14 h≤endpointMeanCorner 19 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 19 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint19_14

namespace EndpointAnalyticJoint19_15
private noncomputable def weights : IntegerLookupTree := (.branch 1451 (.branch 1080 (.branch 957 (.branch 929 (.leaf (81135306500000:ℤ)) (.leaf (2168849700000:ℤ))) (.branch 988 (.leaf (2276660100000:ℤ)) (.branch 1032 (.leaf (3050992900000:ℤ)) (.leaf (3052656300000:ℤ))))) (.branch 1222 (.branch 1119 (.leaf (2250697300000:ℤ)) (.branch 1161 (.leaf (2238985600000:ℤ)) (.leaf (2980429300000:ℤ)))) (.branch 1308 (.leaf (3685265800000:ℤ)) (.branch 1386 (.leaf (2780089300000:ℤ)) (.leaf (1959929700000:ℤ)))))) (.branch 2063 (.branch 1658 (.branch 1522 (.leaf (1853806300000:ℤ)) (.leaf (2969608600000:ℤ))) (.branch 1785 (.leaf (2042884200000:ℤ)) (.branch 1934 (.leaf (1772941500000:ℤ)) (.leaf (1096576500000:ℤ))))) (.branch 2813 (.branch 2264 (.leaf (1218305000000:ℤ)) (.branch 2509 (.leaf (900484700000:ℤ)) (.leaf (601183900000:ℤ)))) (.branch 3201 (.leaf (350475300000:ℤ)) (.branch 4420 (.leaf (293353600000:ℤ)) (.leaf (27463700000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 141 (.branch 129 (.branch 121 (.leaf (1865827085659437:ℤ)) (.leaf (1990424539307095:ℤ))) (.branch 133 (.leaf (2098775822935164:ℤ)) (.branch 137 (.leaf (2156118397600093:ℤ)) (.leaf (2215720433326755:ℤ))))) (.branch 152 (.branch 145 (.leaf (2277702407799018:ℤ)) (.branch 148 (.leaf (2342193018698885:ℤ)) (.leaf (2392289692527066:ℤ)))) (.branch 156 (.leaf (2461507316970920:ℤ)) (.branch 161 (.leaf (2533635753964729:ℤ)) (.leaf (2628144042674240:ℤ)))))) (.branch 183 (.branch 171 (.branch 167 (.leaf (2687302231326704:ℤ)) (.leaf (2748399158908805:ℤ))) (.branch 176 (.leaf (2833027156273281:ℤ)) (.branch 180 (.leaf (2944208756930963:ℤ)) (.leaf (3037760319161911:ℤ))))) (.branch 194 (.branch 186 (.leaf (3110778897562468:ℤ)) (.branch 190 (.leaf (3186373464558732:ℤ)) (.leaf (3291388140345707:ℤ)))) (.branch 197 (.leaf (3401517501185571:ℤ)) (.branch 200 (.leaf (3487675055678099:ℤ)) (.leaf (3577055295618326:ℤ))))))), (.branch 164 (.branch 141 (.branch 129 (.branch 121 (.leaf (1874392726653960:ℤ)) (.leaf (2001515177477581:ℤ))) (.branch 133 (.leaf (2112300945540335:ℤ)) (.branch 137 (.leaf (2171019496762288:ℤ)) (.leaf (2232114724043152:ℤ))))) (.branch 152 (.branch 145 (.leaf (2295716588105019:ℤ)) (.branch 148 (.leaf (2361964110589794:ℤ)) (.leaf (2413475118707437:ℤ)))) (.branch 156 (.leaf (2484717122245981:ℤ)) (.branch 161 (.leaf (2559040413986055:ℤ)) (.leaf (2656553937137736:ℤ)))))) (.branch 183 (.branch 171 (.branch 167 (.leaf (2717666631019869:ℤ)) (.leaf (2780840423669496:ℤ))) (.branch 176 (.leaf (2868441526808363:ℤ)) (.branch 180 (.leaf (2983695943317504:ℤ)) (.leaf (3080818188201487:ℤ))))) (.branch 194 (.branch 186 (.leaf (3156713181424292:ℤ)) (.branch 190 (.leaf (3235366844527692:ℤ)) (.leaf (3344765867886379:ℤ)))) (.branch 197 (.leaf (3459658090189455:ℤ)) (.branch 200 (.leaf (3549657182337076:ℤ)) (.leaf (3643127733261674:ℤ))))))), (.branch 164 (.branch 141 (.branch 129 (.branch 121 (.leaf (1870688955645474:ℤ)) (.leaf (1996966237997467:ℤ))) (.branch 133 (.leaf (2107007278687061:ℤ)) (.branch 137 (.leaf (2165332291527536:ℤ)) (.leaf (2226021190601358:ℤ))))) (.branch 152 (.branch 145 (.leaf (2289205303075030:ℤ)) (.branch 148 (.leaf (2355025376335552:ℤ)) (.leaf (2406210707078636:ℤ)))) (.branch 156 (.leaf (2477013749635564:ℤ)) (.branch 161 (.leaf (2550895522267536:ℤ)) (.leaf (2647859274958527:ℤ)))))) (.branch 183 (.branch 171 (.branch 167 (.leaf (2708646634054669:ℤ)) (.leaf (2771501248382912:ℤ))) (.branch 176 (.leaf (2858690964494104:ℤ)) (.branch 180 (.leaf (2973464415490774:ℤ)) (.leaf (3070239283695166:ℤ))))) (.branch 194 (.branch 186 (.leaf (3145902430573121:ℤ)) (.branch 190 (.leaf (3224354574011635:ℤ)) (.leaf (3333542407422717:ℤ)))) (.branch 197 (.leaf (3448304177619735:ℤ)) (.branch 200 (.leaf (3538269805294822:ℤ)) (.leaf (3631772317423226:ℤ))))))), (.branch 164 (.branch 141 (.branch 129 (.branch 121 (.leaf (1879602981323118:ℤ)) (.leaf (2008532637669968:ℤ))) (.branch 133 (.leaf (2121138901165808:ℤ)) (.branch 137 (.leaf (2180916981188934:ℤ)) (.leaf (2243185208455811:ℤ))))) (.branch 152 (.branch 145 (.leaf (2308085462223981:ℤ)) (.branch 148 (.leaf (2375770018177663:ℤ)) (.leaf (2428458600622646:ℤ)))) (.branch 156 (.leaf (2501416775385583:ℤ)) (.branch 161 (.leaf (2577639647564221:ℤ)) (.leaf (2677816148257143:ℤ)))))) (.branch 183 (.branch 171 (.branch 167 (.leaf (2740697328112963:ℤ)) (.leaf (2805780489559168:ℤ))) (.branch 176 (.leaf (2896166800394137:ℤ)) (.branch 180 (.leaf (3015330951272793:ℤ)) (.leaf (3115965952278832:ℤ))))) (.branch 194 (.branch 186 (.leaf (3194745758018190:ℤ)) (.branch 190 (.leaf (3276519239141626:ℤ)) (.leaf (3390479057227889:ℤ)))) (.branch 197 (.leaf (3510440068673897:ℤ)) (.branch 200 (.leaf (3604610458147007:ℤ)) (.leaf (3702600789849821:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 19 15) 8000 (endpointMeanRuns 19 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 19 15, EndpointRunConditions (endpointMeanCutoff 19 15) (endpointMeanBox 19 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 19 15 h) (endpointMeanCornerA 19 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 15, endpointJoint24Q (endpointMeanCornerK 19 15 h) (endpointMeanCornerA 19 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 19 15, endpointRunWeightQ (endpointMeanCutoff 19 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 19 15) = (218361029/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 19 15 h = (logRoundedQ ((endpointMeanCutoff 19 15:ℚ)/200)).2+(218361029/500000000000000:ℚ)+((endpointMeanRuns 19 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 19 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 19 15) r*endpointJoint24Q (endpointMeanCornerK 19 15 h) (endpointMeanCornerA 19 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 19 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 19 15 h≤endpointMeanCorner 19 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 19 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint19_15

namespace EndpointAnalyticJoint19_16
private noncomputable def weights : IntegerLookupTree := (.branch 1386 (.branch 1080 (.branch 957 (.branch 929 (.leaf (78143442600000:ℤ)) (.leaf (2153196000000:ℤ))) (.branch 988 (.leaf (2260537600000:ℤ)) (.branch 1032 (.leaf (3029870800000:ℤ)) (.leaf (3032070800000:ℤ))))) (.branch 1222 (.branch 1119 (.leaf (2235872300000:ℤ)) (.branch 1161 (.leaf (2224535300000:ℤ)) (.leaf (2961650400000:ℤ)))) (.branch 1255 (.leaf (1413176900000:ℤ)) (.branch 1308 (.leaf (2112281000000:ℤ)) (.leaf (2763667100000:ℤ)))))) (.branch 2063 (.branch 1658 (.branch 1451 (.leaf (1948653900000:ℤ)) (.branch 1522 (.leaf (1843383400000:ℤ)) (.leaf (2953419900000:ℤ)))) (.branch 1785 (.leaf (2032154300000:ℤ)) (.branch 1934 (.leaf (1763941800000:ℤ)) (.leaf (1091183900000:ℤ))))) (.branch 2813 (.branch 2264 (.leaf (1212501900000:ℤ)) (.branch 2509 (.leaf (896359400000:ℤ)) (.leaf (598541100000:ℤ)))) (.branch 3201 (.leaf (349001000000:ℤ)) (.branch 4420 (.leaf (292188700000:ℤ)) (.leaf (27365200000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 141 (.branch 129 (.branch 121 (.leaf (1874392726653960:ℤ)) (.leaf (2001515177477581:ℤ))) (.branch 133 (.leaf (2112300945540335:ℤ)) (.branch 137 (.leaf (2171019496762288:ℤ)) (.leaf (2232114724043152:ℤ))))) (.branch 152 (.branch 145 (.leaf (2295716588105019:ℤ)) (.branch 148 (.leaf (2361964110589794:ℤ)) (.leaf (2413475118707437:ℤ)))) (.branch 156 (.leaf (2484717122245981:ℤ)) (.branch 161 (.leaf (2559040413986055:ℤ)) (.leaf (2656553937137736:ℤ)))))) (.branch 183 (.branch 174 (.branch 167 (.leaf (2717666631019869:ℤ)) (.branch 171 (.leaf (2780840423669496:ℤ)) (.leaf (2868441526808363:ℤ)))) (.branch 176 (.leaf (2936799544410077:ℤ)) (.branch 180 (.leaf (2983695943317504:ℤ)) (.leaf (3080818188201487:ℤ))))) (.branch 194 (.branch 186 (.leaf (3156713181424292:ℤ)) (.branch 190 (.leaf (3235366844527692:ℤ)) (.leaf (3344765867886379:ℤ)))) (.branch 197 (.leaf (3459658090189455:ℤ)) (.branch 200 (.leaf (3549657182337076:ℤ)) (.leaf (3643127733261674:ℤ))))))), (.branch 164 (.branch 141 (.branch 129 (.branch 121 (.leaf (1882997690802386:ℤ)) (.leaf (2012667612642929:ℤ))) (.branch 133 (.leaf (2125913227974338:ℤ)) (.branch 137 (.leaf (2186023578560539:ℤ)) (.leaf (2248630317413104:ℤ))))) (.branch 152 (.branch 145 (.leaf (2313873241234063:ℤ)) (.branch 148 (.leaf (2381902095675005:ℤ)) (.leaf (2434848156899781:ℤ)))) (.branch 156 (.leaf (2508145775158503:ℤ)) (.branch 161 (.leaf (2584699805473733:ℤ)) (.leaf (2685270938856512:ℤ)))))) (.branch 183 (.branch 174 (.branch 167 (.leaf (2748374124525847:ℤ)) (.branch 171 (.leaf (2813664615217175:ℤ)) (.leaf (2904298596114484:ℤ)))) (.branch 176 (.leaf (2975100806461453:ℤ)) (.branch 180 (.leaf (3023712724585880:ℤ)) (.leaf (3124486368750676:ℤ))))) (.branch 194 (.branch 186 (.leaf (3203325738639309:ℤ)) (.branch 190 (.leaf (3285113542118546:ℤ)) (.leaf (3399009242891256:ℤ)))) (.branch 197 (.leaf (3518792449793823:ℤ)) (.branch 200 (.leaf (3612740840521742:ℤ)) (.leaf (3710420606893662:ℤ))))))), (.branch 164 (.branch 141 (.branch 129 (.branch 121 (.leaf (1879602981323118:ℤ)) (.leaf (2008532637669968:ℤ))) (.branch 133 (.leaf (2121138901165808:ℤ)) (.branch 137 (.leaf (2180916981188934:ℤ)) (.leaf (2243185208455811:ℤ))))) (.branch 152 (.branch 145 (.leaf (2308085462223981:ℤ)) (.branch 148 (.leaf (2375770018177663:ℤ)) (.leaf (2428458600622646:ℤ)))) (.branch 156 (.leaf (2501416775385583:ℤ)) (.branch 161 (.leaf (2577639647564221:ℤ)) (.leaf (2677816148257143:ℤ)))))) (.branch 183 (.branch 174 (.branch 167 (.leaf (2740697328112963:ℤ)) (.branch 171 (.leaf (2805780489559168:ℤ)) (.leaf (2896166800394137:ℤ)))) (.branch 176 (.leaf (2966809925911438:ℤ)) (.branch 180 (.leaf (3015330951272793:ℤ)) (.leaf (3115965952278832:ℤ))))) (.branch 194 (.branch 186 (.leaf (3194745758018190:ℤ)) (.branch 190 (.leaf (3276519239141626:ℤ)) (.leaf (3390479057227889:ℤ)))) (.branch 197 (.leaf (3510440068673897:ℤ)) (.branch 200 (.leaf (3604610458147007:ℤ)) (.leaf (3702600789849821:ℤ))))))), (.branch 164 (.branch 141 (.branch 129 (.branch 121 (.leaf (1888559483251848:ℤ)) (.leaf (2020166029762689:ℤ))) (.branch 133 (.leaf (2135365303931220:ℤ)) (.branch 137 (.leaf (2196613839570486:ℤ)) (.leaf (2260481571640196:ℤ))))) (.branch 152 (.branch 145 (.leaf (2327121334977567:ℤ)) (.branch 148 (.leaf (2396697392728086:ℤ)) (.leaf (2450912198831545:ℤ)))) (.branch 156 (.leaf (2526060214684315:ℤ)) (.branch 161 (.leaf (2604664163896779:ℤ)) (.leaf (2708111942232664:ℤ)))))) (.branch 183 (.branch 174 (.branch 167 (.leaf (2773127269495992:ℤ)) (.branch 171 (.leaf (2840483712639205:ℤ)) (.leaf (2934133923493046:ℤ)))) (.branch 176 (.leaf (3007412971589671:ℤ)) (.branch 180 (.leaf (3057786970086543:ℤ)) (.leaf (3162373651891859:ℤ))))) (.branch 194 (.branch 186 (.leaf (3244347427684162:ℤ)) (.branch 190 (.leaf (3329527841321854:ℤ)) (.leaf (3448388180664661:ℤ)))) (.branch 197 (.leaf (3573695602531654:ℤ)) (.branch 200 (.leaf (3672194962503755:ℤ)) (.leaf (3774810591299220:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 19 16) 8000 (endpointMeanRuns 19 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 19 16, EndpointRunConditions (endpointMeanCutoff 19 16) (endpointMeanBox 19 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 19 16 h) (endpointMeanCornerA 19 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 16, endpointJoint24Q (endpointMeanCornerK 19 16 h) (endpointMeanCornerA 19 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 19 16, endpointRunWeightQ (endpointMeanCutoff 19 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 19 16) = (87078243/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 19 16 h = (logRoundedQ ((endpointMeanCutoff 19 16:ℚ)/200)).2+(87078243/200000000000000:ℚ)+((endpointMeanRuns 19 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 19 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 19 16) r*endpointJoint24Q (endpointMeanCornerK 19 16 h) (endpointMeanCornerA 19 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 19 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 19 16 h≤endpointMeanCorner 19 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 19 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint19_16

namespace EndpointAnalyticJoint19_17
private noncomputable def weights : IntegerLookupTree := (.branch 1386 (.branch 1080 (.branch 957 (.branch 929 (.leaf (74779170700000:ℤ)) (.leaf (2135159200000:ℤ))) (.branch 988 (.leaf (2241960700000:ℤ)) (.branch 1032 (.leaf (3005533100000:ℤ)) (.leaf (3008351400000:ℤ))))) (.branch 1222 (.branch 1119 (.leaf (2218790500000:ℤ)) (.branch 1161 (.leaf (2207885000000:ℤ)) (.leaf (2940012600000:ℤ)))) (.branch 1255 (.leaf (1403072100000:ℤ)) (.branch 1308 (.leaf (2097444900000:ℤ)) (.leaf (2744744800000:ℤ)))))) (.branch 2063 (.branch 1658 (.branch 1451 (.leaf (1935661600000:ℤ)) (.branch 1522 (.leaf (1831373700000:ℤ)) (.leaf (2934766700000:ℤ)))) (.branch 1785 (.leaf (2019790900000:ℤ)) (.branch 1934 (.leaf (1753572100000:ℤ)) (.leaf (1084970300000:ℤ))))) (.branch 2813 (.branch 2264 (.leaf (1205815400000:ℤ)) (.branch 2509 (.leaf (891606000000:ℤ)) (.leaf (595496100000:ℤ)))) (.branch 3201 (.leaf (347302400000:ℤ)) (.branch 4420 (.leaf (290846600000:ℤ)) (.leaf (27251700000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 141 (.branch 129 (.branch 121 (.leaf (1882997690802386:ℤ)) (.leaf (2012667612642929:ℤ))) (.branch 133 (.leaf (2125913227974338:ℤ)) (.branch 137 (.leaf (2186023578560539:ℤ)) (.leaf (2248630317413104:ℤ))))) (.branch 152 (.branch 145 (.leaf (2313873241234063:ℤ)) (.branch 148 (.leaf (2381902095675005:ℤ)) (.leaf (2434848156899781:ℤ)))) (.branch 156 (.leaf (2508145775158503:ℤ)) (.branch 161 (.leaf (2584699805473733:ℤ)) (.leaf (2685270938856512:ℤ)))))) (.branch 183 (.branch 174 (.branch 167 (.leaf (2748374124525847:ℤ)) (.branch 171 (.leaf (2813664615217175:ℤ)) (.leaf (2904298596114484:ℤ)))) (.branch 176 (.leaf (2975100806461453:ℤ)) (.branch 180 (.leaf (3023712724585880:ℤ)) (.leaf (3124486368750676:ℤ))))) (.branch 194 (.branch 186 (.leaf (3203325738639309:ℤ)) (.branch 190 (.leaf (3285113542118546:ℤ)) (.leaf (3399009242891256:ℤ)))) (.branch 197 (.leaf (3518792449793823:ℤ)) (.branch 200 (.leaf (3612740840521742:ℤ)) (.leaf (3710420606893662:ℤ))))))), (.branch 164 (.branch 141 (.branch 129 (.branch 121 (.leaf (1891642158629496:ℤ)) (.leaf (2023882189135767:ℤ))) (.branch 133 (.leaf (2139613231920490:ℤ)) (.branch 137 (.leaf (2201131354715724:ℤ)) (.leaf (2265268110964530:ℤ))))) (.branch 152 (.branch 145 (.leaf (2332173493993205:ℤ)) (.branch 148 (.leaf (2402008382745619:ℤ)) (.leaf (2456410468541868:ℤ)))) (.branch 156 (.leaf (2531795339245332:ℤ)) (.branch 161 (.leaf (2610616482609541:ℤ)) (.leaf (2714298367619957:ℤ)))))) (.branch 183 (.branch 174 (.branch 167 (.leaf (2779428588534629:ℤ)) (.branch 171 (.leaf (2846876253502743:ℤ)) (.leaf (2940603898165530:ℤ)))) (.branch 176 (.leaf (3013901587343625:ℤ)) (.branch 180 (.leaf (3064266203565253:ℤ)) (.leaf (3168773511496264:ℤ))))) (.branch 194 (.branch 186 (.leaf (3250626584705813:ℤ)) (.branch 190 (.leaf (3335625140272491:ℤ)) (.leaf (3454132303903504:ℤ)))) (.branch 197 (.leaf (3578937566066811:ℤ)) (.branch 200 (.leaf (3676945606386818:ℤ)) (.leaf (3778956459408964:ℤ))))))), (.branch 164 (.branch 141 (.branch 129 (.branch 121 (.leaf (1888559483251848:ℤ)) (.leaf (2020166029762689:ℤ))) (.branch 133 (.leaf (2135365303931220:ℤ)) (.branch 137 (.leaf (2196613839570486:ℤ)) (.leaf (2260481571640196:ℤ))))) (.branch 152 (.branch 145 (.leaf (2327121334977567:ℤ)) (.branch 148 (.leaf (2396697392728086:ℤ)) (.leaf (2450912198831545:ℤ)))) (.branch 156 (.leaf (2526060214684315:ℤ)) (.branch 161 (.leaf (2604664163896779:ℤ)) (.leaf (2708111942232664:ℤ)))))) (.branch 183 (.branch 174 (.branch 167 (.leaf (2773127269495992:ℤ)) (.branch 171 (.leaf (2840483712639205:ℤ)) (.leaf (2934133923493046:ℤ)))) (.branch 176 (.leaf (3007412971589671:ℤ)) (.branch 180 (.leaf (3057786970086543:ℤ)) (.leaf (3162373651891859:ℤ))))) (.branch 194 (.branch 186 (.leaf (3244347427684162:ℤ)) (.branch 190 (.leaf (3329527841321854:ℤ)) (.leaf (3448388180664661:ℤ)))) (.branch 197 (.leaf (3573695602531654:ℤ)) (.branch 200 (.leaf (3672194962503755:ℤ)) (.leaf (3774810591299220:ℤ))))))), (.branch 164 (.branch 141 (.branch 129 (.branch 121 (.leaf (1897558663835374:ℤ)) (.leaf (2031866802294764:ℤ))) (.branch 133 (.leaf (2149687122671290:ℤ)) (.branch 137 (.leaf (2212423673991548:ℤ)) (.leaf (2277911300619916:ℤ))))) (.branch 152 (.branch 145 (.leaf (2346314205579550:ℤ)) (.branch 148 (.leaf (2417809109618982:ℤ)) (.leaf (2473573403656588:ℤ)))) (.branch 156 (.leaf (2550946436036179:ℤ)) (.branch 161 (.leaf (2631972010943810:ℤ)) (.leaf (2738750491304801:ℤ)))))) (.branch 183 (.branch 174 (.branch 167 (.leaf (2805940945736321:ℤ)) (.branch 171 (.leaf (2875616161632188:ℤ)) (.leaf (2972598774290583:ℤ)))) (.branch 176 (.leaf (3048571700766176:ℤ)) (.branch 180 (.leaf (3100840771884199:ℤ)) (.leaf (3209472525483151:ℤ))))) (.branch 194 (.branch 186 (.leaf (3294719213603498:ℤ)) (.branch 190 (.leaf (3383394034042543:ℤ)) (.leaf (3507286387508409:ℤ)))) (.branch 197 (.leaf (3638090954328292:ℤ)) (.branch 200 (.leaf (3741046639910727:ℤ)) (.leaf (3848428661077108:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 19 17) 8000 (endpointMeanRuns 19 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 19 17, EndpointRunConditions (endpointMeanCutoff 19 17) (endpointMeanBox 19 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 19 17 h) (endpointMeanCornerA 19 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 17, endpointJoint24Q (endpointMeanCornerK 19 17 h) (endpointMeanCornerA 19 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 19 17, endpointRunWeightQ (endpointMeanCutoff 19 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 19 17) = (86771553/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 19 17 h = (logRoundedQ ((endpointMeanCutoff 19 17:ℚ)/200)).2+(86771553/200000000000000:ℚ)+((endpointMeanRuns 19 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 19 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 19 17) r*endpointJoint24Q (endpointMeanCornerK 19 17 h) (endpointMeanCornerA 19 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 19 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 19 17 h≤endpointMeanCorner 19 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 19 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint19_17

namespace EndpointAnalyticJoint19_18
private noncomputable def weights : IntegerLookupTree := (.branch 1451 (.branch 1080 (.branch 988 (.branch 929 (.leaf (71999762700000:ℤ)) (.leaf (4500926100000:ℤ))) (.branch 1032 (.leaf (2984927200000:ℤ)) (.leaf (2988268900000:ℤ)))) (.branch 1222 (.branch 1161 (.leaf (4587162600000:ℤ)) (.leaf (2921692600000:ℤ))) (.branch 1308 (.leaf (3614896000000:ℤ)) (.branch 1386 (.leaf (2728723900000:ℤ)) (.leaf (1924661400000:ℤ)))))) (.branch 2063 (.branch 1658 (.branch 1522 (.leaf (1821205600000:ℤ)) (.leaf (2918973700000:ℤ))) (.branch 1785 (.leaf (2009323300000:ℤ)) (.branch 1934 (.leaf (1744792300000:ℤ)) (.leaf (1079709500000:ℤ))))) (.branch 2509 (.branch 2264 (.leaf (1200154200000:ℤ)) (.leaf (887581400000:ℤ))) (.branch 3201 (.leaf (1117623800000:ℤ)) (.branch 4420 (.leaf (289710200000:ℤ)) (.leaf (27155600000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 141 (.branch 129 (.branch 121 (.leaf (1891642158629496:ℤ)) (.leaf (2023882189135767:ℤ))) (.branch 137 (.leaf (2139613231920490:ℤ)) (.leaf (2265268110964530:ℤ)))) (.branch 148 (.branch 145 (.leaf (2332173493993205:ℤ)) (.leaf (2402008382745619:ℤ))) (.branch 152 (.leaf (2456410468541868:ℤ)) (.branch 156 (.leaf (2531795339245332:ℤ)) (.leaf (2610616482609541:ℤ)))))) (.branch 180 (.branch 167 (.branch 164 (.leaf (2714298367619957:ℤ)) (.leaf (2779428588534629:ℤ))) (.branch 171 (.leaf (2846876253502743:ℤ)) (.branch 176 (.leaf (2940603898165530:ℤ)) (.leaf (3064266203565253:ℤ))))) (.branch 190 (.branch 186 (.leaf (3168773511496264:ℤ)) (.leaf (3335625140272491:ℤ))) (.branch 194 (.leaf (3454132303903504:ℤ)) (.branch 200 (.leaf (3578937566066811:ℤ)) (.leaf (3778956459408964:ℤ))))))), (.branch 161 (.branch 141 (.branch 129 (.branch 121 (.leaf (1900326311488818:ℤ)) (.leaf (2035159253207335:ℤ))) (.branch 137 (.leaf (2153401522681771:ℤ)) (.leaf (2282029008866250:ℤ)))) (.branch 148 (.branch 145 (.leaf (2350618482101316:ℤ)) (.leaf (2422284392484724:ℤ))) (.branch 152 (.leaf (2478163729784663:ℤ)) (.branch 156 (.leaf (2555667897500616:ℤ)) (.leaf (2636793025185951:ℤ)))))) (.branch 180 (.branch 167 (.branch 164 (.leaf (2743639579103956:ℤ)) (.leaf (2810833943539751:ℤ))) (.branch 171 (.leaf (2880479911829239:ℤ)) (.branch 176 (.leaf (2977363036113058:ℤ)) (.leaf (3105363578346613:ℤ))))) (.branch 190 (.branch 186 (.leaf (3213688389741739:ℤ)) (.leaf (3386913400028953:ℤ))) (.branch 194 (.leaf (3510149317134833:ℤ)) (.branch 200 (.leaf (3640110715411691:ℤ)) (.leaf (3848758250096147:ℤ))))))), (.branch 161 (.branch 141 (.branch 129 (.branch 121 (.leaf (1897558663835374:ℤ)) (.leaf (2031866802294764:ℤ))) (.branch 137 (.leaf (2149687122671290:ℤ)) (.leaf (2277911300619916:ℤ)))) (.branch 148 (.branch 145 (.leaf (2346314205579550:ℤ)) (.leaf (2417809109618982:ℤ))) (.branch 152 (.leaf (2473573403656588:ℤ)) (.branch 156 (.leaf (2550946436036179:ℤ)) (.leaf (2631972010943810:ℤ)))))) (.branch 180 (.branch 167 (.branch 164 (.leaf (2738750491304801:ℤ)) (.leaf (2805940945736321:ℤ))) (.branch 171 (.leaf (2875616161632188:ℤ)) (.branch 176 (.leaf (2972598774290583:ℤ)) (.leaf (3100840771884199:ℤ))))) (.branch 190 (.branch 186 (.leaf (3209472525483151:ℤ)) (.leaf (3383394034042543:ℤ))) (.branch 194 (.leaf (3507286387508409:ℤ)) (.branch 200 (.leaf (3638090954328292:ℤ)) (.leaf (3848428661077108:ℤ))))))), (.branch 161 (.branch 141 (.branch 129 (.branch 121 (.leaf (1906600726441888:ℤ)) (.leaf (2043635345532723:ℤ))) (.branch 137 (.leaf (2164104997337556:ℤ)) (.leaf (2295475423728796:ℤ)))) (.branch 148 (.branch 145 (.leaf (2365665368865466:ℤ)) (.leaf (2439106792661228:ℤ))) (.branch 152 (.leaf (2496444134634533:ℤ)) (.branch 156 (.leaf (2576077831279620:ℤ)) (.leaf (2659566159204136:ℤ)))))) (.branch 180 (.branch 167 (.branch 164 (.leaf (2769735673274424:ℤ)) (.leaf (2839142897466296:ℤ))) (.branch 171 (.leaf (2911183145407658:ℤ)) (.branch 176 (.leaf (3011567877717846:ℤ)) (.leaf (3144500773481699:ℤ))))) (.branch 190 (.branch 186 (.leaf (3257272867065816:ℤ)) (.leaf (3438131691684531:ℤ))) (.branch 194 (.leaf (3567190571228212:ℤ)) (.branch 200 (.leaf (3703646662740099:ℤ)) (.leaf (3923482463871722:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 19 18) 8000 (endpointMeanRuns 19 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 19 18, EndpointRunConditions (endpointMeanCutoff 19 18) (endpointMeanBox 19 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 19 18 h) (endpointMeanCornerA 19 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 18, endpointJoint24Q (endpointMeanCornerK 19 18 h) (endpointMeanCornerA 19 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 19 18, endpointRunWeightQ (endpointMeanCutoff 19 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 19 18) = (108139861/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 19 18 h = (logRoundedQ ((endpointMeanCutoff 19 18:ℚ)/200)).2+(108139861/250000000000000:ℚ)+((endpointMeanRuns 19 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 19 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 19 18) r*endpointJoint24Q (endpointMeanCornerK 19 18 h) (endpointMeanCornerA 19 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 19 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 19 18 h≤endpointMeanCorner 19 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 19 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint19_18

namespace EndpointAnalyticJoint19_19
private noncomputable def weights : IntegerLookupTree := (.branch 1386 (.branch 1080 (.branch 929 (.leaf (69313086400000:ℤ)) (.branch 988 (.leaf (4469167000000:ℤ)) (.leaf (6247237700000:ℤ)))) (.branch 1222 (.branch 1161 (.leaf (4557693800000:ℤ)) (.leaf (2903576900000:ℤ))) (.branch 1308 (.leaf (3593192400000:ℤ)) (.leaf (2712881700000:ℤ))))) (.branch 1934 (.branch 1522 (.leaf (3939356900000:ℤ)) (.branch 1658 (.leaf (2903356800000:ℤ)) (.leaf (4109248200000:ℤ)))) (.branch 2509 (.branch 2264 (.leaf (2506021600000:ℤ)) (.leaf (883601800000:ℤ))) (.branch 3201 (.leaf (1112883600000:ℤ)) (.leaf (721947400000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 167 (.branch 141 (.branch 129 (.leaf (1900326311488818:ℤ)) (.branch 137 (.leaf (2153401522681771:ℤ)) (.leaf (2282029008866250:ℤ)))) (.branch 156 (.branch 148 (.leaf (2350618482101316:ℤ)) (.leaf (2478163729784663:ℤ))) (.branch 161 (.leaf (2636793025185951:ℤ)) (.leaf (2743639579103956:ℤ))))) (.branch 180 (.branch 171 (.leaf (2880479911829239:ℤ)) (.branch 176 (.leaf (2977363036113058:ℤ)) (.leaf (3105363578346613:ℤ)))) (.branch 194 (.branch 186 (.leaf (3213688389741739:ℤ)) (.leaf (3386913400028953:ℤ))) (.branch 200 (.leaf (3640110715411691:ℤ)) (.leaf (3848758250096147:ℤ)))))), (.branch 167 (.branch 141 (.branch 129 (.leaf (1909050331566440:ℤ)) (.branch 137 (.leaf (2167278669204121:ℤ)) (.leaf (2298913921977074:ℤ)))) (.branch 156 (.branch 148 (.leaf (2369209350259595:ℤ)) (.leaf (2500109631622653:ℤ))) (.branch 161 (.leaf (2663232038862891:ℤ)) (.leaf (2773297965258807:ℤ))))) (.branch 180 (.branch 171 (.leaf (2914480217481567:ℤ)) (.branch 176 (.leaf (3014581683151040:ℤ)) (.leaf (3147012143560435:ℤ)))) (.branch 194 (.branch 186 (.leaf (3259239901145270:ℤ)) (.leaf (3438990263263989:ℤ))) (.branch 200 (.leaf (3702329469529404:ℤ)) (.leaf (3919849362328968:ℤ)))))), (.branch 167 (.branch 141 (.branch 129 (.leaf (1906600726441888:ℤ)) (.branch 137 (.leaf (2164104997337556:ℤ)) (.leaf (2295475423728796:ℤ)))) (.branch 156 (.branch 148 (.leaf (2365665368865466:ℤ)) (.leaf (2496444134634533:ℤ))) (.branch 161 (.leaf (2659566159204136:ℤ)) (.leaf (2769735673274424:ℤ))))) (.branch 180 (.branch 171 (.leaf (2911183145407658:ℤ)) (.branch 176 (.leaf (3011567877717846:ℤ)) (.leaf (3144500773481699:ℤ)))) (.branch 194 (.branch 186 (.leaf (3257272867065816:ℤ)) (.leaf (3438131691684531:ℤ))) (.branch 200 (.leaf (3703646662740099:ℤ)) (.leaf (3923482463871722:ℤ)))))), (.branch 167 (.branch 141 (.branch 129 (.leaf (1915685875408653:ℤ)) (.branch 137 (.leaf (2178619572173667:ℤ)) (.leaf (2313174977229762:ℤ)))) (.branch 156 (.branch 148 (.leaf (2385176130349958:ℤ)) (.leaf (2519526329050226:ℤ))) (.branch 161 (.leaf (2687449610319904:ℤ)) (.leaf (2801071409814360:ℤ))))) (.branch 180 (.branch 171 (.leaf (2947190038497784:ℤ)) (.branch 176 (.leaf (3051047844244108:ℤ)) (.leaf (3188775510204195:ℤ)))) (.branch 194 (.branch 186 (.leaf (3305785123967047:ℤ)) (.leaf (3493754913092959:ℤ))) (.branch 200 (.leaf (3770383636535135:ℤ)) (.leaf (4000000000000120:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 19 19) 8000 (endpointMeanRuns 19 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 19 19, EndpointRunConditions (endpointMeanCutoff 19 19) (endpointMeanBox 19 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 19 19 h) (endpointMeanCornerA 19 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 19, endpointJoint24Q (endpointMeanCornerK 19 19 h) (endpointMeanCornerA 19 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 19 19, endpointRunWeightQ (endpointMeanCutoff 19 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 19 19) = (215637801/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 19 19 h = (logRoundedQ ((endpointMeanCutoff 19 19:ℚ)/200)).2+(215637801/500000000000000:ℚ)+((endpointMeanRuns 19 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 19 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 19 19) r*endpointJoint24Q (endpointMeanCornerK 19 19 h) (endpointMeanCornerA 19 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 19 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 19 19 h≤endpointMeanCorner 19 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 19 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint19_19

namespace EndpointAnalyticJoint19_20
private noncomputable def weights : IntegerLookupTree := (.branch 1522 (.branch 1080 (.branch 929 (.leaf (66715952800000:ℤ)) (.leaf (11578141700000:ℤ))) (.branch 1161 (.leaf (4528550000000:ℤ)) (.branch 1308 (.leaf (6919801500000:ℤ)) (.leaf (7217117500000:ℤ))))) (.branch 1934 (.branch 1658 (.leaf (2887912100000:ℤ)) (.leaf (4088509600000:ℤ))) (.branch 2264 (.leaf (2494206100000:ℤ)) (.branch 3201 (.leaf (2521258600000:ℤ)) (.leaf (719182200000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 141 (.branch 129 (.leaf (1909050331566440:ℤ)) (.leaf (2167278669204121:ℤ))) (.branch 148 (.leaf (2369209350259595:ℤ)) (.branch 156 (.leaf (2500109631622653:ℤ)) (.leaf (2663232038862891:ℤ))))) (.branch 180 (.branch 171 (.leaf (2773297965258807:ℤ)) (.leaf (3014581683151040:ℤ))) (.branch 186 (.leaf (3259239901145270:ℤ)) (.branch 200 (.leaf (3438990263263989:ℤ)) (.leaf (3919849362328968:ℤ)))))), (.branch 161 (.branch 141 (.branch 129 (.leaf (1917814401884829:ℤ)) (.leaf (2181245244099937:ℤ))) (.branch 148 (.leaf (2387947252222603:ℤ)) (.branch 156 (.leaf (2522249880025271:ℤ)) (.leaf (2689936155427137:ℤ))))) (.branch 180 (.branch 171 (.leaf (2803276954701359:ℤ)) (.leaf (3052265583391458:ℤ))) (.branch 186 (.leaf (3305437069482369:ℤ)) (.branch 200 (.leaf (3491867855470830:ℤ)) (.leaf (3992253611399718:ℤ)))))), (.branch 161 (.branch 141 (.branch 129 (.leaf (1915685875408653:ℤ)) (.leaf (2178619572173667:ℤ))) (.branch 148 (.leaf (2385176130349958:ℤ)) (.branch 156 (.leaf (2519526329050226:ℤ)) (.leaf (2687449610319904:ℤ))))) (.branch 180 (.branch 171 (.leaf (2801071409814360:ℤ)) (.leaf (3051047844244108:ℤ))) (.branch 186 (.leaf (3305785123967047:ℤ)) (.branch 200 (.leaf (3493754913092959:ℤ)) (.leaf (4000000000000120:ℤ)))))), (.branch 161 (.branch 141 (.branch 129 (.leaf (1924814316046610:ℤ)) (.leaf (2193231495744219:ℤ))) (.branch 148 (.leaf (2404847806314885:ℤ)) (.branch 156 (.leaf (2542821942100717:ℤ)) (.leaf (2715625397403116:ℤ))))) (.branch 180 (.branch 171 (.leaf (2832761666965769:ℤ)) (.leaf (3091045370998205:ℤ))) (.branch 186 (.leaf (3355019899111522:ℤ)) (.branch 200 (.leaf (3550278025208698:ℤ)) (.leaf (4078009815854271:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 19 20) 8000 (endpointMeanRuns 19 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 19 20, EndpointRunConditions (endpointMeanCutoff 19 20) (endpointMeanBox 19 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 19 20 h) (endpointMeanCornerA 19 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 19 20, endpointJoint24Q (endpointMeanCornerK 19 20 h) (endpointMeanCornerA 19 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 19 20, endpointRunWeightQ (endpointMeanCutoff 19 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 19 20) = (430005921/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 19 20 h = (logRoundedQ ((endpointMeanCutoff 19 20:ℚ)/200)).2+(430005921/1000000000000000:ℚ)+((endpointMeanRuns 19 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 19 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 19 20) r*endpointJoint24Q (endpointMeanCornerK 19 20 h) (endpointMeanCornerA 19 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 19 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 19 20 h≤endpointMeanCorner 19 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 19 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint19_20

namespace EndpointAnalyticJoint20_05
private noncomputable def weights : IntegerLookupTree := (.branch 1438 (.branch 906 (.leaf (114011234300000:ℤ)) (.leaf (50351992300000:ℤ))) (.branch 2012 (.leaf (14952660300000:ℤ)) (.leaf (17897474300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 145 (.leaf (1783841044368466:ℤ)) (.leaf (2157285030936351:ℤ))) (.branch 200 (.leaf (2393967910681542:ℤ)) (.leaf (2993890135037748:ℤ)))), (.branch 163 (.branch 145 (.leaf (1792341230797828:ℤ)) (.leaf (2176287843291501:ℤ))) (.branch 200 (.leaf (2421876477402694:ℤ)) (.leaf (3052278339568213:ℤ)))), (.branch 163 (.branch 145 (.leaf (1785441979135973:ℤ)) (.leaf (2161409946291500:ℤ))) (.branch 200 (.leaf (2400531499425217:ℤ)) (.leaf (3010320691412704:ℤ)))), (.branch 163 (.branch 145 (.leaf (1794271680055904:ℤ)) (.leaf (2181282298054426:ℤ))) (.branch 200 (.leaf (2429846787894230:ℤ)) (.leaf (3072390546108882:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 20 5) 8000 (endpointMeanRuns 20 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 20 5, EndpointRunConditions (endpointMeanCutoff 20 5) (endpointMeanBox 20 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 20 5 h) (endpointMeanCornerA 20 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 5, endpointJoint24Q (endpointMeanCornerK 20 5 h) (endpointMeanCornerA 20 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 20 5, endpointRunWeightQ (endpointMeanCutoff 20 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 20 5) = (112612071/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 20 5 h = (logRoundedQ ((endpointMeanCutoff 20 5:ℚ)/200)).2+(112612071/250000000000000:ℚ)+((endpointMeanRuns 20 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 20 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 20 5) r*endpointJoint24Q (endpointMeanCornerK 20 5 h) (endpointMeanCornerA 20 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 20 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 20 5 h≤endpointMeanCorner 20 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 20 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint20_05

namespace EndpointAnalyticJoint20_06
private noncomputable def weights : IntegerLookupTree := (.branch 1438 (.branch 906 (.leaf (109858463900000:ℤ)) (.leaf (49998073200000:ℤ))) (.branch 2012 (.leaf (14866776100000:ℤ)) (.leaf (17809049900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 145 (.leaf (1792341230797828:ℤ)) (.leaf (2176287843291501:ℤ))) (.branch 200 (.leaf (2421876477402694:ℤ)) (.leaf (3052278339568213:ℤ)))), (.branch 163 (.branch 145 (.leaf (1800881921491604:ℤ)) (.leaf (2195458045153475:ℤ))) (.branch 200 (.leaf (2450110398566966:ℤ)) (.leaf (3111805257369542:ℤ)))), (.branch 163 (.branch 145 (.leaf (1794271680055904:ℤ)) (.leaf (2181282298054426:ℤ))) (.branch 200 (.leaf (2429846787894230:ℤ)) (.leaf (3072390546108882:ℤ)))), (.branch 163 (.branch 145 (.leaf (1803145047260848:ℤ)) (.leaf (2201337359425615:ℤ))) (.branch 200 (.leaf (2459520074639135:ℤ)) (.leaf (3135740220218651:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 20 6) 8000 (endpointMeanRuns 20 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 20 6, EndpointRunConditions (endpointMeanCutoff 20 6) (endpointMeanBox 20 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 20 6 h) (endpointMeanCornerA 20 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 6, endpointJoint24Q (endpointMeanCornerK 20 6 h) (endpointMeanCornerA 20 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 20 6, endpointRunWeightQ (endpointMeanCutoff 20 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 20 6) = (448949999/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 20 6 h = (logRoundedQ ((endpointMeanCutoff 20 6:ℚ)/200)).2+(448949999/1000000000000000:ℚ)+((endpointMeanRuns 20 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 20 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 20 6) r*endpointJoint24Q (endpointMeanCornerK 20 6 h) (endpointMeanCornerA 20 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 20 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 20 6 h≤endpointMeanCorner 20 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 20 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint20_06

namespace EndpointAnalyticJoint20_07
private noncomputable def weights : IntegerLookupTree := (.branch 1147 (.branch 906 (.leaf (105191943000000:ℤ)) (.leaf (22546012900000:ℤ))) (.branch 1438 (.leaf (15851707500000:ℤ)) (.branch 2012 (.leaf (14767970500000:ℤ)) (.leaf (17707321900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 145 (.leaf (1800881921491604:ℤ)) (.leaf (2195458045153475:ℤ))) (.branch 179 (.leaf (2450110398566966:ℤ)) (.branch 200 (.leaf (2710305317726223:ℤ)) (.leaf (3111805257369542:ℤ))))), (.branch 163 (.branch 145 (.leaf (1809463309456789:ℤ)) (.leaf (2214797111001234:ℤ))) (.branch 179 (.leaf (2478673467114165:ℤ)) (.branch 200 (.leaf (2750111555445333:ℤ)) (.leaf (3172493096144883:ℤ))))), (.branch 163 (.branch 145 (.leaf (1803145047260848:ℤ)) (.leaf (2201337359425615:ℤ))) (.branch 179 (.leaf (2459520074639135:ℤ)) (.branch 200 (.leaf (2724441086613416:ℤ)) (.leaf (3135740220218651:ℤ))))), (.branch 163 (.branch 145 (.leaf (1812062296697467:ℤ)) (.leaf (2221576810266686:ℤ))) (.branch 179 (.leaf (2489555731534549:ℤ)) (.branch 200 (.leaf (2766510088453218:ℤ)) (.leaf (3200396102360764:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 20 7) 8000 (endpointMeanRuns 20 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 20 7, EndpointRunConditions (endpointMeanCutoff 20 7) (endpointMeanBox 20 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 20 7 h) (endpointMeanCornerA 20 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 7, endpointJoint24Q (endpointMeanCornerK 20 7 h) (endpointMeanCornerA 20 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 20 7, endpointRunWeightQ (endpointMeanCutoff 20 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 20 7) = (55903287/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 20 7 h = (logRoundedQ ((endpointMeanCutoff 20 7:ℚ)/200)).2+(55903287/125000000000000:ℚ)+((endpointMeanRuns 20 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 20 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 20 7) r*endpointJoint24Q (endpointMeanCornerK 20 7 h) (endpointMeanCornerA 20 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 20 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 20 7 h≤endpointMeanCorner 20 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 20 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint20_07

namespace EndpointAnalyticJoint20_08
private noncomputable def weights : IntegerLookupTree := (.branch 1147 (.branch 906 (.leaf (101339176600000:ℤ)) (.leaf (22383388300000:ℤ))) (.branch 1438 (.leaf (15750604600000:ℤ)) (.branch 2012 (.leaf (14684441800000:ℤ)) (.leaf (17621322700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 145 (.leaf (1809463309456789:ℤ)) (.leaf (2214797111001234:ℤ))) (.branch 179 (.leaf (2478673467114165:ℤ)) (.branch 200 (.leaf (2750111555445333:ℤ)) (.leaf (3172493096144883:ℤ))))), (.branch 163 (.branch 145 (.leaf (1818085588620076:ℤ)) (.leaf (2234306528301933:ℤ))) (.branch 179 (.leaf (2507569520201696:ℤ)) (.branch 200 (.leaf (2790502427135755:ℤ)) (.leaf (3234364496702088:ℤ))))), (.branch 163 (.branch 145 (.leaf (1812062296697467:ℤ)) (.leaf (2221576810266686:ℤ))) (.branch 179 (.leaf (2489555731534549:ℤ)) (.branch 200 (.leaf (2766510088453218:ℤ)) (.leaf (3200396102360764:ℤ))))), (.branch 163 (.branch 145 (.leaf (1821023645380364:ℤ)) (.leaf (2242002345884171:ℤ))) (.branch 179 (.leaf (2519958183844421:ℤ)) (.branch 200 (.leaf (2809228691756052:ℤ)) (.leaf (3266385125261349:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 20 8) 8000 (endpointMeanRuns 20 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 20 8, EndpointRunConditions (endpointMeanCutoff 20 8) (endpointMeanBox 20 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 20 8 h) (endpointMeanCornerA 20 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 8, endpointJoint24Q (endpointMeanCornerK 20 8 h) (endpointMeanCornerA 20 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 20 8, endpointRunWeightQ (endpointMeanCutoff 20 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 20 8) = (27860569/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 20 8 h = (logRoundedQ ((endpointMeanCutoff 20 8:ℚ)/200)).2+(27860569/62500000000000:ℚ)+((endpointMeanRuns 20 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 20 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 20 8) r*endpointJoint24Q (endpointMeanCornerK 20 8 h) (endpointMeanCornerA 20 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 20 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 20 8 h≤endpointMeanCorner 20 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 20 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint20_08

namespace EndpointAnalyticJoint20_09
private noncomputable def weights : IntegerLookupTree := (.branch 1438 (.branch 906 (.leaf (97617083800000:ℤ)) (.branch 1147 (.leaf (22222796500000:ℤ)) (.leaf (15650765600000:ℤ)))) (.branch 2012 (.leaf (14601957300000:ℤ)) (.branch 3122 (.leaf (5864073000000:ℤ)) (.leaf (927235600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 129 (.leaf (1818085588620076:ℤ)) (.branch 145 (.leaf (2024172861394110:ℤ)) (.leaf (2234306528301933:ℤ)))) (.branch 179 (.leaf (2507569520201696:ℤ)) (.branch 200 (.leaf (2790502427135755:ℤ)) (.leaf (3234364496702088:ℤ))))), (.branch 163 (.branch 129 (.leaf (1826748953832236:ℤ)) (.branch 145 (.leaf (2037748916397945:ℤ)) (.leaf (2253987797625338:ℤ)))) (.branch 179 (.leaf (2536802439720046:ℤ)) (.branch 200 (.leaf (2831486519313056:ℤ)) (.leaf (3297442541400315:ℤ))))), (.branch 163 (.branch 129 (.leaf (1821023645380364:ℤ)) (.branch 145 (.leaf (2029130454032475:ℤ)) (.leaf (2242002345884171:ℤ)))) (.branch 179 (.leaf (2519958183844421:ℤ)) (.branch 200 (.leaf (2809228691756052:ℤ)) (.leaf (3266385125261349:ℤ))))), (.branch 163 (.branch 129 (.leaf (1830029311397363:ℤ)) (.branch 145 (.leaf (2043295051540709:ℤ)) (.leaf (2262615677171532:ℤ)))) (.branch 179 (.leaf (2550731910874012:ℤ)) (.branch 200 (.leaf (2852606927234370:ℤ)) (.leaf (3333734776972901:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 20 9) 8000 (endpointMeanRuns 20 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 20 9, EndpointRunConditions (endpointMeanCutoff 20 9) (endpointMeanBox 20 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 20 9 h) (endpointMeanCornerA 20 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 9, endpointJoint24Q (endpointMeanCornerK 20 9 h) (endpointMeanCornerA 20 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 20 9, endpointRunWeightQ (endpointMeanCutoff 20 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 20 9) = (27770633/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 20 9 h = (logRoundedQ ((endpointMeanCutoff 20 9:ℚ)/200)).2+(27770633/62500000000000:ℚ)+((endpointMeanRuns 20 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 20 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 20 9) r*endpointJoint24Q (endpointMeanCornerK 20 9 h) (endpointMeanCornerA 20 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 20 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 20 9 h≤endpointMeanCorner 20 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 20 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint20_09

namespace EndpointAnalyticJoint20_10
private noncomputable def weights : IntegerLookupTree := (.branch 1438 (.branch 906 (.leaf (93433606800000:ℤ)) (.branch 1147 (.leaf (22037941800000:ℤ)) (.leaf (15535842400000:ℤ)))) (.branch 2012 (.leaf (14507010700000:ℤ)) (.branch 3122 (.leaf (5830992200000:ℤ)) (.leaf (922744000000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 129 (.leaf (1826748953832236:ℤ)) (.branch 145 (.leaf (2037748916397945:ℤ)) (.leaf (2253987797625338:ℤ)))) (.branch 179 (.leaf (2536802439720046:ℤ)) (.branch 200 (.leaf (2831486519313056:ℤ)) (.leaf (3297442541400315:ℤ))))), (.branch 163 (.branch 129 (.leaf (1835453600872531:ℤ)) (.branch 145 (.leaf (2051416025517264:ℤ)) (.leaf (2273842432759246:ℤ)))) (.branch 179 (.leaf (2566376152814287:ℤ)) (.branch 200 (.leaf (2873072544602929:ℤ)) (.leaf (3361750762761384:ℤ))))), (.branch 163 (.branch 129 (.leaf (1830029311397363:ℤ)) (.branch 145 (.leaf (2043295051540709:ℤ)) (.leaf (2262615677171532:ℤ)))) (.branch 179 (.leaf (2550731910874012:ℤ)) (.branch 200 (.leaf (2852606927234370:ℤ)) (.leaf (3333734776972901:ℤ))))), (.branch 163 (.branch 129 (.leaf (1839079513914817:ℤ)) (.branch 145 (.leaf (2057558526783578:ℤ)) (.leaf (2283418530752457:ℤ)))) (.branch 179 (.leaf (2581881446629864:ℤ)) (.branch 200 (.leaf (2896654980488204:ℤ)) (.leaf (3402473112324540:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 20 10) 8000 (endpointMeanRuns 20 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 20 10, EndpointRunConditions (endpointMeanCutoff 20 10) (endpointMeanBox 20 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 20 10 h) (endpointMeanCornerA 20 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 10, endpointJoint24Q (endpointMeanCornerK 20 10 h) (endpointMeanCornerA 20 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 20 10, endpointRunWeightQ (endpointMeanCutoff 20 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 20 10) = (88534749/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 20 10 h = (logRoundedQ ((endpointMeanCutoff 20 10:ℚ)/200)).2+(88534749/200000000000000:ℚ)+((endpointMeanRuns 20 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 20 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 20 10) r*endpointJoint24Q (endpointMeanCornerK 20 10 h) (endpointMeanCornerA 20 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 20 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 20 10 h≤endpointMeanCorner 20 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 20 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint20_10

namespace EndpointAnalyticJoint20_11
private noncomputable def weights : IntegerLookupTree := (.branch 1438 (.branch 906 (.leaf (89978934800000:ℤ)) (.branch 1147 (.leaf (21881584800000:ℤ)) (.leaf (15438636100000:ℤ)))) (.branch 2012 (.leaf (14426701200000:ℤ)) (.branch 3122 (.leaf (5803011300000:ℤ)) (.leaf (918944800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 129 (.leaf (1835453600872531:ℤ)) (.branch 145 (.leaf (2051416025517264:ℤ)) (.leaf (2273842432759246:ℤ)))) (.branch 179 (.leaf (2566376152814287:ℤ)) (.branch 200 (.leaf (2873072544602929:ℤ)) (.leaf (3361750762761384:ℤ))))), (.branch 163 (.branch 129 (.leaf (1844199726453122:ℤ)) (.branch 145 (.leaf (2065174799448753:ℤ)) (.leaf (2293871960825895:ℤ)))) (.branch 179 (.leaf (2596294632411616:ℤ)) (.branch 200 (.leaf (2915269343593331:ℤ)) (.leaf (3427313152249024:ℤ))))), (.branch 163 (.branch 129 (.leaf (1839079513914817:ℤ)) (.branch 145 (.leaf (2057558526783578:ℤ)) (.leaf (2283418530752457:ℤ)))) (.branch 179 (.leaf (2581881446629864:ℤ)) (.branch 200 (.leaf (2896654980488204:ℤ)) (.leaf (3402473112324540:ℤ))))), (.branch 163 (.branch 129 (.leaf (1848174473182942:ℤ)) (.branch 145 (.leaf (2071921569989403:ℤ)) (.leaf (2304412649125487:ℤ)))) (.branch 179 (.leaf (2613411380487785:ℤ)) (.branch 200 (.leaf (2941383194396805:ℤ)) (.leaf (3472628764608390:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 20 11) 8000 (endpointMeanRuns 20 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 20 11, EndpointRunConditions (endpointMeanCutoff 20 11) (endpointMeanBox 20 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 20 11 h) (endpointMeanCornerA 20 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 11, endpointJoint24Q (endpointMeanCornerK 20 11 h) (endpointMeanCornerA 20 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 20 11, endpointRunWeightQ (endpointMeanCutoff 20 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 20 11) = (220636357/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 20 11 h = (logRoundedQ ((endpointMeanCutoff 20 11:ℚ)/200)).2+(220636357/500000000000000:ℚ)+((endpointMeanRuns 20 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 20 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 20 11) r*endpointJoint24Q (endpointMeanCornerK 20 11 h) (endpointMeanCornerA 20 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 20 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 20 11 h≤endpointMeanCorner 20 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 20 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint20_11

namespace EndpointAnalyticJoint20_12
private noncomputable def weights : IntegerLookupTree := (.branch 1438 (.branch 985 (.branch 906 (.leaf (86640831400000:ℤ)) (.leaf (6954395000000:ℤ))) (.branch 1147 (.leaf (12280782000000:ℤ)) (.leaf (15342598600000:ℤ)))) (.branch 2012 (.branch 1709 (.leaf (7354520400000:ℤ)) (.leaf (4316347500000:ℤ))) (.branch 3122 (.leaf (5775366800000:ℤ)) (.leaf (915191300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 145 (.branch 129 (.leaf (1844199726453122:ℤ)) (.leaf (2065174799448753:ℤ))) (.branch 153 (.leaf (2293871960825895:ℤ)) (.leaf (2421752502278534:ℤ)))) (.branch 192 (.branch 179 (.leaf (2596294632411616:ℤ)) (.leaf (2915269343593331:ℤ))) (.branch 200 (.leaf (3217844613990415:ℤ)) (.leaf (3427313152249024:ℤ))))), (.branch 163 (.branch 145 (.branch 129 (.leaf (1852987528223535:ℤ)) (.leaf (2079025852985038:ℤ))) (.branch 153 (.leaf (2314077922399453:ℤ)) (.leaf (2445987858964377:ℤ)))) (.branch 192 (.branch 179 (.leaf (2626561897755117:ℤ)) (.leaf (2958085886713900:ℤ))) (.branch 200 (.leaf (3274300988331998:ℤ)) (.leaf (3494154169219382:ℤ))))), (.branch 163 (.branch 145 (.branch 129 (.leaf (1848174473182942:ℤ)) (.leaf (2071921569989403:ℤ))) (.branch 153 (.leaf (2304412649125487:ℤ)) (.leaf (2434850342079301:ℤ)))) (.branch 192 (.branch 179 (.leaf (2613411380487785:ℤ)) (.leaf (2941383194396805:ℤ))) (.branch 200 (.leaf (3254571580113632:ℤ)) (.leaf (3472628764608390:ℤ))))), (.branch 163 (.branch 145 (.branch 129 (.leaf (1857314410541170:ℤ)) (.leaf (2086384876204736:ℤ))) (.branch 153 (.leaf (2325599790809979:ℤ)) (.leaf (2460322407406354:ℤ)))) (.branch 192 (.branch 179 (.leaf (2645326357869061:ℤ)) (.leaf (2986802071547301:ℤ))) (.branch 200 (.leaf (3314805785407155:ℤ)) (.leaf (3544230957506935:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 20 12) 8000 (endpointMeanRuns 20 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 20 12, EndpointRunConditions (endpointMeanCutoff 20 12) (endpointMeanBox 20 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 20 12 h) (endpointMeanCornerA 20 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 12, endpointJoint24Q (endpointMeanCornerK 20 12 h) (endpointMeanCornerA 20 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 20 12, endpointRunWeightQ (endpointMeanCutoff 20 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 20 12) = (43988853/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 20 12 h = (logRoundedQ ((endpointMeanCutoff 20 12:ℚ)/200)).2+(43988853/100000000000000:ℚ)+((endpointMeanRuns 20 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 20 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 20 12) r*endpointJoint24Q (endpointMeanCornerK 20 12 h) (endpointMeanCornerA 20 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 20 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 20 12 h≤endpointMeanCorner 20 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 20 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint20_12

namespace EndpointAnalyticJoint20_13
private noncomputable def weights : IntegerLookupTree := (.branch 1438 (.branch 985 (.branch 906 (.leaf (82888250100000:ℤ)) (.leaf (6895284800000:ℤ))) (.branch 1147 (.leaf (12183160700000:ℤ)) (.branch 1276 (.leaf (6876629200000:ℤ)) (.leaf (6480822500000:ℤ))))) (.branch 2012 (.branch 1709 (.leaf (7306613800000:ℤ)) (.leaf (4290287800000:ℤ))) (.branch 2447 (.leaf (2828395100000:ℤ)) (.branch 3122 (.leaf (1369000500000:ℤ)) (.leaf (910868500000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 137 (.branch 129 (.leaf (1852987528223535:ℤ)) (.leaf (2079025852985038:ℤ))) (.branch 145 (.leaf (2192086148002014:ℤ)) (.branch 153 (.leaf (2314077922399453:ℤ)) (.leaf (2445987858964377:ℤ))))) (.branch 179 (.branch 171 (.leaf (2626561897755117:ℤ)) (.leaf (2785187807907364:ℤ))) (.branch 192 (.leaf (2958085886713900:ℤ)) (.branch 200 (.leaf (3274300988331998:ℤ)) (.leaf (3494154169219382:ℤ)))))), (.branch 163 (.branch 137 (.branch 129 (.leaf (1861817204775098:ℤ)) (.leaf (2092969805042118:ℤ))) (.branch 145 (.leaf (2208988505419661:ℤ)) (.branch 153 (.leaf (2334461871624502:ℤ)) (.leaf (2470465747664999:ℤ))))) (.branch 179 (.branch 171 (.leaf (2657182014943681:ℤ)) (.leaf (2821700058632018:ℤ))) (.branch 192 (.leaf (3001531276142891:ℤ)) (.branch 200 (.leaf (3331747877314943:ℤ)) (.leaf (3562298750046089:ℤ)))))), (.branch 163 (.branch 137 (.branch 129 (.leaf (1857314410541170:ℤ)) (.leaf (2086384876204736:ℤ))) (.branch 145 (.leaf (2201314658432085:ℤ)) (.branch 153 (.leaf (2325599790809979:ℤ)) (.leaf (2460322407406354:ℤ))))) (.branch 179 (.branch 171 (.leaf (2645326357869061:ℤ)) (.leaf (2808414163627589:ℤ))) (.branch 192 (.leaf (2986802071547301:ℤ)) (.branch 200 (.leaf (3314805785407155:ℤ)) (.leaf (3544230957506935:ℤ)))))), (.branch 163 (.branch 137 (.branch 129 (.leaf (1866499548423550:ℤ)) (.leaf (2100949145327987:ℤ))) (.branch 145 (.leaf (2219005152062628:ℤ)) (.branch 153 (.leaf (2346981730493400:ℤ)) (.leaf (2486060947473476:ℤ))))) (.branch 179 (.branch 171 (.leaf (2677631080924846:ℤ)) (.leaf (2847049070558809:ℤ))) (.branch 192 (.leaf (3032922276700736:ℤ)) (.branch 200 (.leaf (3376154779359654:ℤ)) (.leaf (3617309517266267:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 20 13) 8000 (endpointMeanRuns 20 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 20 13, EndpointRunConditions (endpointMeanCutoff 20 13) (endpointMeanBox 20 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 20 13 h) (endpointMeanCornerA 20 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 13, endpointJoint24Q (endpointMeanCornerK 20 13 h) (endpointMeanCornerA 20 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 20 13, endpointRunWeightQ (endpointMeanCutoff 20 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 20 13) = (438294407/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 20 13 h = (logRoundedQ ((endpointMeanCutoff 20 13:ℚ)/200)).2+(438294407/1000000000000000:ℚ)+((endpointMeanRuns 20 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 20 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 20 13) r*endpointJoint24Q (endpointMeanCornerK 20 13 h) (endpointMeanCornerA 20 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 20 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 20 13 h≤endpointMeanCorner 20 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 20 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint20_13

namespace EndpointAnalyticJoint20_14
private noncomputable def weights : IntegerLookupTree := (.branch 1438 (.branch 1066 (.branch 906 (.leaf (79788867200000:ℤ)) (.branch 985 (.leaf (6845262400000:ℤ)) (.leaf (6009066200000:ℤ)))) (.branch 1276 (.branch 1147 (.leaf (5095818000000:ℤ)) (.leaf (6833327000000:ℤ))) (.branch 1352 (.leaf (3071983700000:ℤ)) (.leaf (2940004900000:ℤ))))) (.branch 2012 (.branch 1589 (.leaf (4192444300000:ℤ)) (.branch 1709 (.leaf (2392355500000:ℤ)) (.leaf (4268234700000:ℤ)))) (.branch 3122 (.branch 2447 (.leaf (2814874500000:ℤ)) (.leaf (1362958400000:ℤ))) (.branch 4312 (.leaf (368907800000:ℤ)) (.leaf (36809900000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 137 (.branch 121 (.leaf (1861817204775098:ℤ)) (.branch 129 (.leaf (1985466444960519:ℤ)) (.leaf (2092969805042118:ℤ)))) (.branch 153 (.branch 145 (.leaf (2208988505419661:ℤ)) (.leaf (2334461871624502:ℤ))) (.branch 157 (.leaf (2470465747664999:ℤ)) (.leaf (2542796209182140:ℤ))))) (.branch 179 (.branch 167 (.leaf (2657182014943681:ℤ)) (.branch 171 (.leaf (2737640809169244:ℤ)) (.leaf (2821700058632018:ℤ)))) (.branch 192 (.branch 185 (.leaf (3001531276142891:ℤ)) (.leaf (3147653096977900:ℤ))) (.branch 200 (.leaf (3331747877314943:ℤ)) (.leaf (3562298750046089:ℤ)))))), (.branch 163 (.branch 137 (.branch 121 (.leaf (1870688955645474:ℤ)) (.branch 129 (.leaf (1996966237997467:ℤ)) (.leaf (2107007278687061:ℤ)))) (.branch 153 (.branch 145 (.leaf (2226021190601358:ℤ)) (.leaf (2355025376335552:ℤ))) (.branch 157 (.leaf (2495188595486353:ℤ)) (.leaf (2569868308206404:ℤ))))) (.branch 179 (.branch 167 (.leaf (2688159097478253:ℤ)) (.branch 171 (.leaf (2771501248382912:ℤ)) (.leaf (2858690964494104:ℤ)))) (.branch 192 (.branch 185 (.leaf (3045614747742222:ℤ)) (.leaf (3197885398713288:ℤ))) (.branch 200 (.leaf (3390202659300272:ℤ)) (.leaf (3631772317423226:ℤ)))))), (.branch 163 (.branch 137 (.branch 121 (.leaf (1866499548423550:ℤ)) (.branch 129 (.leaf (1991788901623633:ℤ)) (.leaf (2100949145327987:ℤ)))) (.branch 153 (.branch 145 (.leaf (2219005152062628:ℤ)) (.leaf (2346981730493400:ℤ))) (.branch 157 (.leaf (2486060947473476:ℤ)) (.leaf (2560183852583838:ℤ))))) (.branch 179 (.branch 167 (.leaf (2677631080924846:ℤ)) (.branch 171 (.leaf (2760412257784306:ℤ)) (.leaf (2847049070558809:ℤ)))) (.branch 192 (.branch 185 (.leaf (3032922276700736:ℤ)) (.leaf (3184492809584080:ℤ))) (.branch 200 (.leaf (3376154779359654:ℤ)) (.leaf (3617309517266267:ℤ)))))), (.branch 163 (.branch 137 (.branch 121 (.leaf (1875730110364151:ℤ)) (.branch 129 (.leaf (2003780308066139:ℤ)) (.leaf (2115615082143290:ℤ)))) (.branch 153 (.branch 145 (.leaf (2236837812358761:ℤ)) (.leaf (2368560259179983:ℤ))) (.branch 157 (.leaf (2512068749992868:ℤ)) (.leaf (2588700856327495:ℤ))))) (.branch 179 (.branch 167 (.leaf (2710330309228953:ℤ)) (.branch 171 (.leaf (2796208313525210:ℤ)) (.leaf (2886215471759262:ℤ)))) (.branch 192 (.branch 185 (.leaf (3079754639296294:ℤ)) (.leaf (3238003126914188:ℤ))) (.branch 200 (.leaf (3438639193998204:ℤ)) (.leaf (3691894885120362:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 20 14) 8000 (endpointMeanRuns 20 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 20 14, EndpointRunConditions (endpointMeanCutoff 20 14) (endpointMeanBox 20 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 20 14 h) (endpointMeanCornerA 20 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 14, endpointJoint24Q (endpointMeanCornerK 20 14 h) (endpointMeanCornerA 20 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 20 14, endpointRunWeightQ (endpointMeanCutoff 20 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 20 14) = (436945369/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 20 14 h = (logRoundedQ ((endpointMeanCutoff 20 14:ℚ)/200)).2+(436945369/1000000000000000:ℚ)+((endpointMeanRuns 20 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 20 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 20 14) r*endpointJoint24Q (endpointMeanCornerK 20 14 h) (endpointMeanCornerA 20 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 20 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 20 14 h≤endpointMeanCorner 20 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 20 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint20_14

namespace EndpointAnalyticJoint20_15
private noncomputable def weights : IntegerLookupTree := (.branch 1438 (.branch 1066 (.branch 934 (.branch 906 (.leaf (76793611700000:ℤ)) (.leaf (2376906000000:ℤ))) (.branch 985 (.leaf (4130093500000:ℤ)) (.leaf (5967762000000:ℤ)))) (.branch 1208 (.branch 1147 (.leaf (5062309600000:ℤ)) (.leaf (3226095200000:ℤ))) (.branch 1276 (.leaf (3162210400000:ℤ)) (.branch 1352 (.leaf (3053587600000:ℤ)) (.leaf (2922925100000:ℤ)))))) (.branch 2012 (.branch 1709 (.branch 1589 (.leaf (4169007600000:ℤ)) (.leaf (2379527300000:ℤ))) (.branch 1848 (.leaf (2081315800000:ℤ)) (.leaf (1761622100000:ℤ)))) (.branch 2447 (.branch 2209 (.leaf (1417792300000:ℤ)) (.leaf (1052593300000:ℤ))) (.branch 3122 (.leaf (1356986300000:ℤ)) (.branch 4312 (.leaf (367429100000:ℤ)) (.leaf (36676700000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 141 (.branch 129 (.branch 121 (.leaf (1870688955645474:ℤ)) (.leaf (1996966237997467:ℤ))) (.branch 137 (.leaf (2107007278687061:ℤ)) (.leaf (2226021190601358:ℤ)))) (.branch 149 (.branch 145 (.leaf (2289205303075030:ℤ)) (.leaf (2355025376335552:ℤ))) (.branch 153 (.leaf (2423632413141722:ℤ)) (.branch 157 (.leaf (2495188595486353:ℤ)) (.leaf (2569868308206404:ℤ)))))) (.branch 179 (.branch 171 (.branch 167 (.leaf (2688159097478253:ℤ)) (.leaf (2771501248382912:ℤ))) (.branch 175 (.leaf (2858690964494104:ℤ)) (.leaf (2949973588778962:ℤ)))) (.branch 192 (.branch 185 (.leaf (3045614747742222:ℤ)) (.leaf (3197885398713288:ℤ))) (.branch 197 (.leaf (3390202659300272:ℤ)) (.branch 200 (.leaf (3538269805294822:ℤ)) (.leaf (3631772317423226:ℤ))))))), (.branch 163 (.branch 141 (.branch 129 (.branch 121 (.leaf (1879602981323118:ℤ)) (.leaf (2008532637669968:ℤ))) (.branch 137 (.leaf (2121138901165808:ℤ)) (.leaf (2243185208455811:ℤ)))) (.branch 149 (.branch 145 (.leaf (2308085462223981:ℤ)) (.leaf (2375770018177663:ℤ))) (.branch 153 (.leaf (2446402486936371:ℤ)) (.branch 157 (.leaf (2520158853823303:ℤ)) (.leaf (2597228632666477:ℤ)))))) (.branch 179 (.branch 171 (.branch 167 (.leaf (2719497306814433:ℤ)) (.leaf (2805780489559168:ℤ))) (.branch 175 (.leaf (2896166800394137:ℤ)) (.leaf (2990924783869720:ℤ)))) (.branch 192 (.branch 185 (.leaf (3090345673020840:ℤ)) (.leaf (3248919340292680:ℤ))) (.branch 197 (.leaf (3449683017548506:ℤ)) (.branch 200 (.leaf (3604610458147007:ℤ)) (.leaf (3702600789849821:ℤ))))))), (.branch 163 (.branch 141 (.branch 129 (.branch 121 (.leaf (1875730110364151:ℤ)) (.leaf (2003780308066139:ℤ))) (.branch 137 (.leaf (2115615082143290:ℤ)) (.leaf (2236837812358761:ℤ)))) (.branch 149 (.branch 145 (.leaf (2301310637878112:ℤ)) (.leaf (2368560259179983:ℤ))) (.branch 153 (.leaf (2438753137524006:ℤ)) (.branch 157 (.leaf (2512068749992868:ℤ)) (.leaf (2588700856327495:ℤ)))))) (.branch 179 (.branch 171 (.branch 167 (.leaf (2710330309228953:ℤ)) (.leaf (2796208313525210:ℤ))) (.branch 175 (.leaf (2886215471759262:ℤ)) (.leaf (2980629996494341:ℤ)))) (.branch 192 (.branch 185 (.leaf (3079754639296294:ℤ)) (.leaf (3238003126914188:ℤ))) (.branch 197 (.leaf (3438639193998204:ℤ)) (.branch 200 (.leaf (3593704290687373:ℤ)) (.leaf (3691894885120362:ℤ))))))), (.branch 163 (.branch 141 (.branch 129 (.branch 121 (.leaf (1885006321002506:ℤ)) (.leaf (2015843907816053:ℤ))) (.branch 137 (.leaf (2130383396354608:ℤ)) (.leaf (2254813781818883:ℤ)))) (.branch 149 (.branch 145 (.leaf (2321106604692375:ℤ)) (.leaf (2390337184340739:ℤ))) (.branch 153 (.leaf (2462686168881912:ℤ)) (.branch 157 (.leaf (2538348631840234:ℤ)) (.leaf (2617535501127161:ℤ)))))) (.branch 179 (.branch 171 (.branch 167 (.leaf (2743428860479114:ℤ)) (.leaf (2832468559932923:ℤ))) (.branch 175 (.leaf (2925920678911057:ℤ)) (.leaf (3024090339828213:ℤ)))) (.branch 192 (.branch 185 (.leaf (3127310155994124:ℤ)) (.leaf (3292412599692900:ℤ))) (.branch 197 (.leaf (3502280043198522:ℤ)) (.branch 200 (.leaf (3664880540498279:ℤ)) (.leaf (3768018129971542:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 20 15) 8000 (endpointMeanRuns 20 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 20 15, EndpointRunConditions (endpointMeanCutoff 20 15) (endpointMeanBox 20 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 20 15 h) (endpointMeanCornerA 20 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 15, endpointJoint24Q (endpointMeanCornerK 20 15 h) (endpointMeanCornerA 20 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 20 15, endpointRunWeightQ (endpointMeanCutoff 20 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 20 15) = (435611957/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 20 15 h = (logRoundedQ ((endpointMeanCutoff 20 15:ℚ)/200)).2+(435611957/1000000000000000:ℚ)+((endpointMeanRuns 20 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 20 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 20 15) r*endpointJoint24Q (endpointMeanCornerK 20 15 h) (endpointMeanCornerA 20 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 20 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 20 15 h≤endpointMeanCorner 20 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 20 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint20_15

namespace EndpointAnalyticJoint20_16
private noncomputable def weights : IntegerLookupTree := (.branch 1352 (.branch 1066 (.branch 934 (.branch 906 (.leaf (73425930700000:ℤ)) (.leaf (2356667300000:ℤ))) (.branch 985 (.leaf (4095826100000:ℤ)) (.branch 1018 (.leaf (2395554600000:ℤ)) (.leaf (3272932600000:ℤ))))) (.branch 1147 (.branch 1105 (.leaf (2415183700000:ℤ)) (.leaf (2404155600000:ℤ))) (.branch 1208 (.leaf (3202351300000:ℤ)) (.branch 1276 (.leaf (3139599700000:ℤ)) (.leaf (3032391400000:ℤ)))))) (.branch 2012 (.branch 1589 (.branch 1438 (.leaf (2903245500000:ℤ)) (.leaf (4142003700000:ℤ))) (.branch 1709 (.leaf (2364746500000:ℤ)) (.branch 1848 (.leaf (2068823600000:ℤ)) (.leaf (1751419900000:ℤ))))) (.branch 2447 (.branch 2209 (.leaf (1409884100000:ℤ)) (.leaf (1046949900000:ℤ))) (.branch 3122 (.leaf (1350105100000:ℤ)) (.branch 4312 (.leaf (365725400000:ℤ)) (.leaf (36523300000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 167 (.branch 145 (.branch 129 (.branch 121 (.leaf (1879602981323118:ℤ)) (.leaf (2008532637669968:ℤ))) (.branch 137 (.leaf (2121138901165808:ℤ)) (.branch 141 (.leaf (2243185208455811:ℤ)) (.leaf (2308085462223981:ℤ))))) (.branch 153 (.branch 149 (.leaf (2375770018177663:ℤ)) (.leaf (2446402486936371:ℤ))) (.branch 157 (.leaf (2520158853823303:ℤ)) (.branch 163 (.leaf (2597228632666477:ℤ)) (.leaf (2719497306814433:ℤ)))))) (.branch 185 (.branch 175 (.branch 171 (.leaf (2805780489559168:ℤ)) (.leaf (2896166800394137:ℤ))) (.branch 179 (.leaf (2990924783869720:ℤ)) (.branch 182 (.leaf (3090345673020840:ℤ)) (.leaf (3168160624707073:ℤ))))) (.branch 192 (.branch 189 (.leaf (3248919340292680:ℤ)) (.leaf (3361442716777110:ℤ))) (.branch 197 (.leaf (3449683017548506:ℤ)) (.branch 200 (.leaf (3604610458147007:ℤ)) (.leaf (3702600789849821:ℤ))))))), (.branch 167 (.branch 145 (.branch 129 (.branch 121 (.leaf (1888559483251848:ℤ)) (.leaf (2020166029762689:ℤ))) (.branch 137 (.leaf (2135365303931220:ℤ)) (.branch 141 (.leaf (2260481571640196:ℤ)) (.leaf (2327121334977567:ℤ))))) (.branch 153 (.branch 149 (.leaf (2396697392728086:ℤ)) (.leaf (2469386486018454:ℤ))) (.branch 157 (.leaf (2545378998602722:ℤ)) (.branch 163 (.leaf (2624880251179318:ℤ)) (.leaf (2751200852921537:ℤ)))))) (.branch 185 (.branch 175 (.branch 171 (.leaf (2840483712639205:ℤ)) (.leaf (2934133923493046:ℤ))) (.branch 179 (.leaf (3032444458754923:ℤ)) (.branch 182 (.leaf (3135733561127008:ℤ)) (.leaf (3216674697597647:ℤ))))) (.branch 192 (.branch 189 (.leaf (3300767714807714:ℤ)) (.leaf (3418086539663183:ℤ))) (.branch 197 (.leaf (3510206945569067:ℤ)) (.branch 200 (.leaf (3672194962503755:ℤ)) (.leaf (3774810591299220:ℤ))))))), (.branch 167 (.branch 145 (.branch 129 (.branch 121 (.leaf (1885006321002506:ℤ)) (.leaf (2015843907816053:ℤ))) (.branch 137 (.leaf (2130383396354608:ℤ)) (.branch 141 (.leaf (2254813781818883:ℤ)) (.leaf (2321106604692375:ℤ))))) (.branch 153 (.branch 149 (.leaf (2390337184340739:ℤ)) (.leaf (2462686168881912:ℤ))) (.branch 157 (.leaf (2538348631840234:ℤ)) (.branch 163 (.leaf (2617535501127161:ℤ)) (.leaf (2743428860479114:ℤ)))))) (.branch 185 (.branch 175 (.branch 171 (.leaf (2832468559932923:ℤ)) (.leaf (2925920678911057:ℤ))) (.branch 179 (.leaf (3024090339828213:ℤ)) (.branch 182 (.leaf (3127310155994124:ℤ)) (.leaf (3208256415788473:ℤ))))) (.branch 192 (.branch 189 (.leaf (3292412599692900:ℤ)) (.leaf (3409922339042717:ℤ))) (.branch 197 (.leaf (3502280043198522:ℤ)) (.branch 200 (.leaf (3664880540498279:ℤ)) (.leaf (3768018129971542:ℤ))))))), (.branch 167 (.branch 145 (.branch 129 (.branch 121 (.leaf (1894328406089069:ℤ)) (.leaf (2027980135507440:ℤ))) (.branch 137 (.leaf (2145254802620096:ℤ)) (.branch 141 (.leaf (2272934212122904:ℤ)) (.leaf (2341072857210647:ℤ))))) (.branch 153 (.branch 149 (.leaf (2412314330064860:ℤ)) (.leaf (2486854070256448:ℤ))) (.branch 157 (.leaf (2564903439359885:ℤ)) (.branch 163 (.leaf (2646691325076860:ℤ)) (.leaf (2776931611206782:ℤ)))))) (.branch 185 (.branch 175 (.branch 171 (.leaf (2869199016468827:ℤ)) (.leaf (2966172104281968:ℤ))) (.branch 179 (.leaf (3068184375181871:ℤ)) (.branch 182 (.leaf (3175599993257481:ℤ)) (.leaf (3259945876616989:ℤ))))) (.branch 192 (.branch 189 (.leaf (3347736336791947:ℤ)) (.leaf (3470487629596302:ℤ))) (.branch 197 (.leaf (3567098729752056:ℤ)) (.branch 200 (.leaf (3737466494093172:ℤ)) (.leaf (3845710961332359:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 20 16) 8000 (endpointMeanRuns 20 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 20 16, EndpointRunConditions (endpointMeanCutoff 20 16) (endpointMeanBox 20 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 20 16 h) (endpointMeanCornerA 20 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 16, endpointJoint24Q (endpointMeanCornerK 20 16 h) (endpointMeanCornerA 20 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 20 16, endpointRunWeightQ (endpointMeanCutoff 20 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 20 16) = (434075583/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 20 16 h = (logRoundedQ ((endpointMeanCutoff 20 16:ℚ)/200)).2+(434075583/1000000000000000:ℚ)+((endpointMeanRuns 20 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 20 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 20 16) r*endpointJoint24Q (endpointMeanCornerK 20 16 h) (endpointMeanCornerA 20 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 20 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 20 16 h≤endpointMeanCorner 20 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 20 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint20_16

namespace EndpointAnalyticJoint20_17
private noncomputable def weights : IntegerLookupTree := (.branch 1352 (.branch 1066 (.branch 934 (.branch 906 (.leaf (70644048500000:ℤ)) (.leaf (2339532300000:ℤ))) (.branch 985 (.leaf (4066813700000:ℤ)) (.branch 1018 (.leaf (2379038100000:ℤ)) (.leaf (3250893300000:ℤ))))) (.branch 1147 (.branch 1105 (.leaf (2399311000000:ℤ)) (.leaf (2388684600000:ℤ))) (.branch 1208 (.leaf (3182248600000:ℤ)) (.branch 1276 (.leaf (3120456400000:ℤ)) (.leaf (3014445700000:ℤ)))))) (.branch 2012 (.branch 1589 (.branch 1438 (.leaf (2886583800000:ℤ)) (.leaf (4119140900000:ℤ))) (.branch 1709 (.leaf (2352232400000:ℤ)) (.branch 1848 (.leaf (2058247100000:ℤ)) (.leaf (1742782300000:ℤ))))) (.branch 2447 (.branch 2209 (.leaf (1403188600000:ℤ)) (.leaf (1042171800000:ℤ))) (.branch 3122 (.leaf (1344279100000:ℤ)) (.branch 4312 (.leaf (364283000000:ℤ)) (.leaf (36393400000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 167 (.branch 145 (.branch 129 (.branch 121 (.leaf (1888559483251848:ℤ)) (.leaf (2020166029762689:ℤ))) (.branch 137 (.leaf (2135365303931220:ℤ)) (.branch 141 (.leaf (2260481571640196:ℤ)) (.leaf (2327121334977567:ℤ))))) (.branch 153 (.branch 149 (.leaf (2396697392728086:ℤ)) (.leaf (2469386486018454:ℤ))) (.branch 157 (.leaf (2545378998602722:ℤ)) (.branch 163 (.leaf (2624880251179318:ℤ)) (.leaf (2751200852921537:ℤ)))))) (.branch 185 (.branch 175 (.branch 171 (.leaf (2840483712639205:ℤ)) (.leaf (2934133923493046:ℤ))) (.branch 179 (.leaf (3032444458754923:ℤ)) (.branch 182 (.leaf (3135733561127008:ℤ)) (.leaf (3216674697597647:ℤ))))) (.branch 192 (.branch 189 (.leaf (3300767714807714:ℤ)) (.leaf (3418086539663183:ℤ))) (.branch 197 (.leaf (3510206945569067:ℤ)) (.branch 200 (.leaf (3672194962503755:ℤ)) (.leaf (3774810591299220:ℤ))))))), (.branch 167 (.branch 145 (.branch 129 (.branch 121 (.leaf (1897558663835374:ℤ)) (.leaf (2031866802294764:ℤ))) (.branch 137 (.leaf (2149687122671290:ℤ)) (.branch 141 (.leaf (2277911300619916:ℤ)) (.leaf (2346314205579550:ℤ))))) (.branch 153 (.branch 149 (.leaf (2417809109618982:ℤ)) (.leaf (2492586420220215:ℤ))) (.branch 157 (.leaf (2570851530528981:ℤ)) (.branch 163 (.leaf (2652826265032155:ℤ)) (.leaf (2783273994848152:ℤ)))))) (.branch 185 (.branch 175 (.branch 171 (.leaf (2875616161632188:ℤ)) (.leaf (2972598774290583:ℤ))) (.branch 179 (.leaf (3074540505005887:ℤ)) (.branch 182 (.leaf (3181788060869762:ℤ)) (.leaf (3265931666934216:ℤ))))) (.branch 192 (.branch 189 (.leaf (3353443519510536:ℤ)) (.leaf (3475684870164435:ℤ))) (.branch 197 (.leaf (3571792752563559:ℤ)) (.branch 200 (.leaf (3741046639910727:ℤ)) (.leaf (3848428661077108:ℤ))))))), (.branch 167 (.branch 145 (.branch 129 (.branch 121 (.leaf (1894328406089069:ℤ)) (.leaf (2027980135507440:ℤ))) (.branch 137 (.leaf (2145254802620096:ℤ)) (.branch 141 (.leaf (2272934212122904:ℤ)) (.leaf (2341072857210647:ℤ))))) (.branch 153 (.branch 149 (.leaf (2412314330064860:ℤ)) (.leaf (2486854070256448:ℤ))) (.branch 157 (.leaf (2564903439359885:ℤ)) (.branch 163 (.leaf (2646691325076860:ℤ)) (.leaf (2776931611206782:ℤ)))))) (.branch 185 (.branch 175 (.branch 171 (.leaf (2869199016468827:ℤ)) (.leaf (2966172104281968:ℤ))) (.branch 179 (.leaf (3068184375181871:ℤ)) (.branch 182 (.leaf (3175599993257481:ℤ)) (.leaf (3259945876616989:ℤ))))) (.branch 192 (.branch 189 (.leaf (3347736336791947:ℤ)) (.leaf (3470487629596302:ℤ))) (.branch 197 (.leaf (3567098729752056:ℤ)) (.branch 200 (.leaf (3737466494093172:ℤ)) (.leaf (3845710961332359:ℤ))))))), (.branch 167 (.branch 145 (.branch 129 (.branch 121 (.leaf (1903696592490732:ℤ)) (.leaf (2040189428391019:ℤ))) (.branch 137 (.leaf (2160230020586656:ℤ)) (.branch 141 (.leaf (2291200264206003:ℤ)) (.leaf (2361210860237411:ℤ))))) (.branch 153 (.branch 149 (.leaf (2434493537212508:ℤ)) (.leaf (2511259146576062:ℤ))) (.branch 157 (.leaf (2591736048673010:ℤ)) (.branch 163 (.leaf (2676171905680216:ℤ)) (.leaf (2810843497495603:ℤ)))))) (.branch 185 (.branch 175 (.branch 171 (.leaf (2906405780652561:ℤ)) (.leaf (3006977262109153:ℤ))) (.branch 179 (.leaf (3112921342371312:ℤ)) (.branch 182 (.leaf (3224635489974681:ℤ)) (.leaf (3312468126354637:ℤ))))) (.branch 192 (.branch 189 (.leaf (3403989700963518:ℤ)) (.leaf (3532128649757517:ℤ))) (.branch 197 (.leaf (3633117052563886:ℤ)) (.branch 200 (.leaf (3811490071807344:ℤ)) (.leaf (3925005742534348:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 20 17) 8000 (endpointMeanRuns 20 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 20 17, EndpointRunConditions (endpointMeanCutoff 20 17) (endpointMeanBox 20 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 20 17 h) (endpointMeanCornerA 20 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 17, endpointJoint24Q (endpointMeanCornerK 20 17 h) (endpointMeanCornerA 20 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 20 17, endpointRunWeightQ (endpointMeanCutoff 20 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 20 17) = (13524213/31250000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 20 17 h = (logRoundedQ ((endpointMeanCutoff 20 17:ℚ)/200)).2+(13524213/31250000000000:ℚ)+((endpointMeanRuns 20 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 20 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 20 17) r*endpointJoint24Q (endpointMeanCornerK 20 17 h) (endpointMeanCornerA 20 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 20 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 20 17 h≤endpointMeanCorner 20 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 20 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint20_17

namespace EndpointAnalyticJoint20_18
private noncomputable def weights : IntegerLookupTree := (.branch 1438 (.branch 1066 (.branch 934 (.branch 906 (.leaf (67955292800000:ℤ)) (.leaf (2322588800000:ℤ))) (.branch 985 (.leaf (4038125500000:ℤ)) (.leaf (5840034800000:ℤ)))) (.branch 1208 (.branch 1147 (.leaf (4958690300000:ℤ)) (.leaf (3162370600000:ℤ))) (.branch 1276 (.leaf (3101527000000:ℤ)) (.branch 1352 (.leaf (2996700500000:ℤ)) (.leaf (2870108300000:ℤ)))))) (.branch 2012 (.branch 1709 (.branch 1589 (.leaf (4096533500000:ℤ)) (.leaf (2339858100000:ℤ))) (.branch 1848 (.leaf (2047788800000:ℤ)) (.leaf (1734241200000:ℤ)))) (.branch 2447 (.branch 2209 (.leaf (1396567900000:ℤ)) (.leaf (1037447100000:ℤ))) (.branch 3122 (.leaf (1338518300000:ℤ)) (.branch 4312 (.leaf (362856700000:ℤ)) (.leaf (36265000000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 141 (.branch 129 (.branch 121 (.leaf (1897558663835374:ℤ)) (.leaf (2031866802294764:ℤ))) (.branch 137 (.leaf (2149687122671290:ℤ)) (.leaf (2277911300619916:ℤ)))) (.branch 149 (.branch 145 (.leaf (2346314205579550:ℤ)) (.leaf (2417809109618982:ℤ))) (.branch 153 (.leaf (2492586420220215:ℤ)) (.branch 157 (.leaf (2570851530528981:ℤ)) (.leaf (2652826265032155:ℤ)))))) (.branch 179 (.branch 171 (.branch 167 (.leaf (2783273994848152:ℤ)) (.leaf (2875616161632188:ℤ))) (.branch 175 (.leaf (2972598774290583:ℤ)) (.leaf (3074540505005887:ℤ)))) (.branch 192 (.branch 185 (.leaf (3181788060869762:ℤ)) (.leaf (3353443519510536:ℤ))) (.branch 197 (.leaf (3571792752563559:ℤ)) (.branch 200 (.leaf (3741046639910727:ℤ)) (.leaf (3848428661077108:ℤ))))))), (.branch 163 (.branch 141 (.branch 129 (.branch 121 (.leaf (1906600726441888:ℤ)) (.leaf (2043635345532723:ℤ))) (.branch 137 (.leaf (2164104997337556:ℤ)) (.leaf (2295475423728796:ℤ)))) (.branch 149 (.branch 145 (.leaf (2365665368865466:ℤ)) (.leaf (2439106792661228:ℤ))) (.branch 153 (.leaf (2516004318256317:ℤ)) (.branch 157 (.leaf (2596578975331903:ℤ)) (.leaf (2681069808530363:ℤ)))))) (.branch 179 (.branch 171 (.branch 167 (.leaf (2815721041294298:ℤ)) (.leaf (2911183145407658:ℤ))) (.branch 175 (.leaf (3011567877717846:ℤ)) (.leaf (3117220923743819:ℤ)))) (.branch 192 (.branch 185 (.leaf (3228518962770172:ℤ)) (.leaf (3406959959071923:ℤ))) (.branch 197 (.leaf (3634459068964473:ℤ)) (.branch 200 (.leaf (3811189249180029:ℤ)) (.leaf (3923482463871722:ℤ))))))), (.branch 163 (.branch 141 (.branch 129 (.branch 121 (.leaf (1903696592490732:ℤ)) (.leaf (2040189428391019:ℤ))) (.branch 137 (.leaf (2160230020586656:ℤ)) (.leaf (2291200264206003:ℤ)))) (.branch 149 (.branch 145 (.leaf (2361210860237411:ℤ)) (.leaf (2434493537212508:ℤ))) (.branch 153 (.leaf (2511259146576062:ℤ)) (.branch 157 (.leaf (2591736048673010:ℤ)) (.leaf (2676171905680216:ℤ)))))) (.branch 179 (.branch 171 (.branch 167 (.leaf (2810843497495603:ℤ)) (.leaf (2906405780652561:ℤ))) (.branch 175 (.leaf (3006977262109153:ℤ)) (.leaf (3112921342371312:ℤ)))) (.branch 192 (.branch 185 (.leaf (3224635489974681:ℤ)) (.leaf (3403989700963518:ℤ))) (.branch 197 (.leaf (3633117052563886:ℤ)) (.branch 200 (.leaf (3811490071807344:ℤ)) (.leaf (3925005742534348:ℤ))))))), (.branch 163 (.branch 141 (.branch 129 (.branch 121 (.leaf (1913111108196315:ℤ)) (.leaf (2052472226349985:ℤ))) (.branch 137 (.leaf (2175309774924783:ℤ)) (.leaf (2309613108333028:ℤ)))) (.branch 149 (.branch 145 (.leaf (2381522091177462:ℤ)) (.leaf (2456876663569011:ℤ))) (.branch 153 (.leaf (2535903725388925:ℤ)) (.branch 157 (.leaf (2618849365989222:ℤ)) (.leaf (2705980860289446:ℤ)))))) (.branch 179 (.branch 171 (.branch 167 (.leaf (2845169515708681:ℤ)) (.leaf (2944095029074261:ℤ))) (.branch 175 (.leaf (3048343770001933:ℤ)) (.leaf (3158310615937609:ℤ)))) (.branch 192 (.branch 185 (.leaf (3274428160121598:ℤ)) (.leaf (3461188313106334:ℤ))) (.branch 197 (.leaf (3700357213983807:ℤ)) (.branch 200 (.leaf (3886979746961124:ℤ)) (.leaf (4005935504209154:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 20 18) 8000 (endpointMeanRuns 20 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 20 18, EndpointRunConditions (endpointMeanCutoff 20 18) (endpointMeanBox 20 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 20 18 h) (endpointMeanCornerA 20 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 18, endpointJoint24Q (endpointMeanCornerK 20 18 h) (endpointMeanCornerA 20 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 20 18, endpointRunWeightQ (endpointMeanCutoff 20 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 20 18) = (53936073/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 20 18 h = (logRoundedQ ((endpointMeanCutoff 20 18:ℚ)/200)).2+(53936073/125000000000000:ℚ)+((endpointMeanRuns 20 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 20 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 20 18) r*endpointJoint24Q (endpointMeanCornerK 20 18 h) (endpointMeanCornerA 20 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 20 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 20 18 h≤endpointMeanCorner 20 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 20 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint20_18

namespace EndpointAnalyticJoint20_19
private noncomputable def weights : IntegerLookupTree := (.branch 1438 (.branch 1066 (.branch 906 (.leaf (64931842300000:ℤ)) (.branch 985 (.leaf (6587947200000:ℤ)) (.leaf (5794107200000:ℤ)))) (.branch 1276 (.branch 1147 (.leaf (4921431300000:ℤ)) (.leaf (6610580400000:ℤ))) (.branch 1352 (.leaf (2976245300000:ℤ)) (.leaf (2851116700000:ℤ))))) (.branch 2012 (.branch 1589 (.leaf (4070473600000:ℤ)) (.branch 1709 (.leaf (2325594100000:ℤ)) (.leaf (4154793200000:ℤ)))) (.branch 3122 (.branch 2447 (.leaf (2745325000000:ℤ)) (.leaf (1331877700000:ℤ))) (.branch 4312 (.leaf (361212500000:ℤ)) (.leaf (36116900000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 137 (.branch 121 (.leaf (1906600726441888:ℤ)) (.branch 129 (.leaf (2043635345532723:ℤ)) (.leaf (2164104997337556:ℤ)))) (.branch 153 (.branch 145 (.leaf (2295475423728796:ℤ)) (.leaf (2439106792661228:ℤ))) (.branch 157 (.leaf (2596578975331903:ℤ)) (.leaf (2681069808530363:ℤ))))) (.branch 179 (.branch 167 (.leaf (2815721041294298:ℤ)) (.branch 171 (.leaf (2911183145407658:ℤ)) (.leaf (3011567877717846:ℤ)))) (.branch 192 (.branch 185 (.leaf (3228518962770172:ℤ)) (.leaf (3406959959071923:ℤ))) (.branch 200 (.leaf (3634459068964473:ℤ)) (.leaf (3923482463871722:ℤ)))))), (.branch 163 (.branch 137 (.branch 121 (.leaf (1915685875408653:ℤ)) (.branch 129 (.leaf (2055472052003526:ℤ)) (.leaf (2178619572173667:ℤ)))) (.branch 153 (.branch 145 (.leaf (2313174977229762:ℤ)) (.leaf (2460592079969319:ℤ))) (.branch 157 (.leaf (2622563884017210:ℤ)) (.leaf (2709614049348949:ℤ))))) (.branch 179 (.branch 167 (.leaf (2848546351190260:ℤ)) (.branch 171 (.leaf (2947190038497784:ℤ)) (.leaf (3051047844244108:ℤ)))) (.branch 192 (.branch 185 (.leaf (3275936201142604:ℤ)) (.leaf (3461330448891399:ℤ))) (.branch 200 (.leaf (3698224852071119:ℤ)) (.leaf (4000000000000120:ℤ)))))), (.branch 163 (.branch 137 (.branch 121 (.leaf (1913111108196315:ℤ)) (.branch 129 (.leaf (2052472226349985:ℤ)) (.leaf (2175309774924783:ℤ)))) (.branch 153 (.branch 145 (.leaf (2309613108333028:ℤ)) (.leaf (2456876663569011:ℤ))) (.branch 157 (.leaf (2618849365989222:ℤ)) (.leaf (2705980860289446:ℤ))))) (.branch 179 (.branch 167 (.leaf (2845169515708681:ℤ)) (.branch 171 (.leaf (2944095029074261:ℤ)) (.leaf (3048343770001933:ℤ)))) (.branch 192 (.branch 185 (.leaf (3274428160121598:ℤ)) (.leaf (3461188313106334:ℤ))) (.branch 200 (.leaf (3700357213983807:ℤ)) (.leaf (4005935504209154:ℤ)))))), (.branch 163 (.branch 137 (.branch 121 (.leaf (1922572182322140:ℤ)) (.branch 129 (.leaf (2064828971915767:ℤ)) (.leaf (2190494795363613:ℤ)))) (.branch 153 (.branch 145 (.leaf (2328173924173457:ℤ)) (.leaf (2479465584000479:ℤ))) (.branch 157 (.leaf (2646246327921270:ℤ)) (.leaf (2736121846549184:ℤ))))) (.branch 179 (.branch 167 (.leaf (2879914723224687:ℤ)) (.branch 171 (.leaf (2982273018419900:ℤ)) (.leaf (3090279350363863:ℤ)))) (.branch 192 (.branch 185 (.leaf (3324989695465235:ℤ)) (.leaf (3519348056603378:ℤ))) (.branch 200 (.leaf (3768841827273121:ℤ)) (.leaf (4088533958047583:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 20 19) 8000 (endpointMeanRuns 20 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 20 19, EndpointRunConditions (endpointMeanCutoff 20 19) (endpointMeanBox 20 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 20 19 h) (endpointMeanCornerA 20 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 19, endpointJoint24Q (endpointMeanCornerK 20 19 h) (endpointMeanCornerA 20 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 20 19, endpointRunWeightQ (endpointMeanCutoff 20 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 20 19) = (430005921/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 20 19 h = (logRoundedQ ((endpointMeanCutoff 20 19:ℚ)/200)).2+(430005921/1000000000000000:ℚ)+((endpointMeanRuns 20 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 20 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 20 19) r*endpointJoint24Q (endpointMeanCornerK 20 19 h) (endpointMeanCornerA 20 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 20 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 20 19 h≤endpointMeanCorner 20 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 20 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint20_19

namespace EndpointAnalyticJoint20_20
private noncomputable def weights : IntegerLookupTree := (.branch 1438 (.branch 985 (.branch 906 (.leaf (62434021600000:ℤ)) (.leaf (6541380900000:ℤ))) (.branch 1147 (.leaf (11598683600000:ℤ)) (.branch 1276 (.leaf (6570270000000:ℤ)) (.leaf (6208446800000:ℤ))))) (.branch 2012 (.branch 1709 (.leaf (7019787800000:ℤ)) (.leaf (4134263700000:ℤ))) (.branch 2447 (.leaf (2732738700000:ℤ)) (.branch 3122 (.leaf (1326253000000:ℤ)) (.leaf (884987000000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 137 (.branch 129 (.leaf (1915685875408653:ℤ)) (.leaf (2178619572173667:ℤ))) (.branch 145 (.leaf (2313174977229762:ℤ)) (.branch 153 (.leaf (2460592079969319:ℤ)) (.leaf (2622563884017210:ℤ))))) (.branch 179 (.branch 171 (.leaf (2848546351190260:ℤ)) (.leaf (3051047844244108:ℤ))) (.branch 192 (.leaf (3275936201142604:ℤ)) (.branch 200 (.leaf (3698224852071119:ℤ)) (.leaf (4000000000000120:ℤ)))))), (.branch 163 (.branch 137 (.branch 129 (.leaf (1924814316046610:ℤ)) (.leaf (2193231495744219:ℤ))) (.branch 145 (.leaf (2331011005375987:ℤ)) (.branch 153 (.leaf (2482266624087368:ℤ)) (.leaf (2648808833119465:ℤ))))) (.branch 179 (.branch 171 (.leaf (2881754334282170:ℤ)) (.leaf (3091045370998205:ℤ))) (.branch 192 (.leaf (3324049856206653:ℤ)) (.branch 200 (.leaf (3763109391784478:ℤ)) (.leaf (4078009815854271:ℤ)))))), (.branch 163 (.branch 137 (.branch 129 (.leaf (1922572182322140:ℤ)) (.leaf (2190494795363613:ℤ))) (.branch 145 (.leaf (2328173924173457:ℤ)) (.branch 153 (.leaf (2479465584000479:ℤ)) (.leaf (2646246327921270:ℤ))))) (.branch 179 (.branch 171 (.leaf (2879914723224687:ℤ)) (.leaf (3090279350363863:ℤ))) (.branch 192 (.leaf (3324989695465235:ℤ)) (.branch 200 (.leaf (3768841827273121:ℤ)) (.leaf (4088533958047583:ℤ)))))), (.branch 163 (.branch 137 (.branch 129 (.leaf (1932080045117605:ℤ)) (.leaf (2205785816726264:ℤ))) (.branch 145 (.leaf (2346883900876982:ℤ)) (.branch 153 (.leaf (2502262190610834:ℤ)) (.leaf (2673929901803153:ℤ))))) (.branch 179 (.branch 171 (.leaf (2915084239183005:ℤ)) (.leaf (3132791831834391:ℤ))) (.branch 192 (.leaf (3376331968309073:ℤ)) (.branch 200 (.leaf (3838593924209598:ℤ)) (.leaf (4172835510842380:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 20 20) 8000 (endpointMeanRuns 20 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 20 20, EndpointRunConditions (endpointMeanCutoff 20 20) (endpointMeanBox 20 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 20 20 h) (endpointMeanCornerA 20 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 20 20, endpointJoint24Q (endpointMeanCornerK 20 20 h) (endpointMeanCornerA 20 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 20 20, endpointRunWeightQ (endpointMeanCutoff 20 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 20 20) = (428750091/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 20 20 h = (logRoundedQ ((endpointMeanCutoff 20 20:ℚ)/200)).2+(428750091/1000000000000000:ℚ)+((endpointMeanRuns 20 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 20 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 20 20) r*endpointJoint24Q (endpointMeanCornerK 20 20 h) (endpointMeanCornerA 20 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 20 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 20 20 h≤endpointMeanCorner 20 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 20 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint20_20

namespace EndpointAnalyticJoint21_05
private noncomputable def weights : IntegerLookupTree := (.branch 1092 (.branch 884 (.leaf (107097263500000:ℤ)) (.leaf (21501668100000:ℤ))) (.branch 1768 (.leaf (41453709200000:ℤ)) (.leaf (33539954400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 181 (.branch 150 (.leaf (1788831432173559:ℤ)) (.leaf (2233193373556879:ℤ))) (.branch 200 (.leaf (2690866190620077:ℤ)) (.leaf (3034033866211889:ℤ)))), (.branch 181 (.branch 150 (.leaf (1794271680055904:ℤ)) (.leaf (2246876300026845:ℤ))) (.branch 200 (.leaf (2717098656375563:ℤ)) (.leaf (3072390546108882:ℤ)))), (.branch 181 (.branch 150 (.leaf (1790621693238284:ℤ)) (.leaf (2238561447092216:ℤ))) (.branch 200 (.leaf (2702883627176027:ℤ)) (.leaf (3053537101920418:ℤ)))), (.branch 181 (.branch 150 (.leaf (1796272783951534:ℤ)) (.leaf (2252895524839202:ℤ))) (.branch 200 (.leaf (2730623912511793:ℤ)) (.leaf (3094406198400057:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 21 5) 8000 (endpointMeanRuns 21 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 21 5, EndpointRunConditions (endpointMeanCutoff 21 5) (endpointMeanBox 21 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 21 5 h) (endpointMeanCornerA 21 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 5, endpointJoint24Q (endpointMeanCornerK 21 5 h) (endpointMeanCornerA 21 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 21 5, endpointRunWeightQ (endpointMeanCutoff 21 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 21 5) = (44870217/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 21 5 h = (logRoundedQ ((endpointMeanCutoff 21 5:ℚ)/200)).2+(44870217/100000000000000:ℚ)+((endpointMeanRuns 21 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 21 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 21 5) r*endpointJoint24Q (endpointMeanCornerK 21 5 h) (endpointMeanCornerA 21 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 21 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 21 5 h≤endpointMeanCorner 21 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 21 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint21_05

namespace EndpointAnalyticJoint21_06
private noncomputable def weights : IntegerLookupTree := (.branch 1092 (.branch 884 (.leaf (103777625800000:ℤ)) (.leaf (21369080100000:ℤ))) (.branch 1768 (.leaf (41234196300000:ℤ)) (.leaf (33396943500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 181 (.branch 150 (.leaf (1794271680055904:ℤ)) (.leaf (2246876300026845:ℤ))) (.branch 200 (.leaf (2717098656375563:ℤ)) (.leaf (3072390546108882:ℤ)))), (.branch 181 (.branch 150 (.leaf (1803145047260848:ℤ)) (.leaf (2269284152883762:ℤ))) (.branch 200 (.leaf (2760261478936141:ℤ)) (.leaf (3135740220218651:ℤ)))), (.branch 181 (.branch 150 (.leaf (1796272783951534:ℤ)) (.leaf (2252895524839202:ℤ))) (.branch 200 (.leaf (2730623912511793:ℤ)) (.leaf (3094406198400057:ℤ)))), (.branch 181 (.branch 150 (.leaf (1805491432060956:ℤ)) (.leaf (2276378197925580:ℤ))) (.branch 200 (.leaf (2776298251603728:ℤ)) (.leaf (3161970368466053:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 21 6) 8000 (endpointMeanRuns 21 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 21 6, EndpointRunConditions (endpointMeanCutoff 21 6) (endpointMeanBox 21 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 21 6 h) (endpointMeanCornerA 21 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 6, endpointJoint24Q (endpointMeanCornerK 21 6 h) (endpointMeanCornerA 21 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 21 6, endpointRunWeightQ (endpointMeanCutoff 21 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 21 6) = (111867741/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 21 6 h = (logRoundedQ ((endpointMeanCutoff 21 6:ℚ)/200)).2+(111867741/250000000000000:ℚ)+((endpointMeanRuns 21 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 21 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 21 6) r*endpointJoint24Q (endpointMeanCornerK 21 6 h) (endpointMeanCornerA 21 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 21 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 21 6 h≤endpointMeanCorner 21 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 21 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint21_06

namespace EndpointAnalyticJoint21_07
private noncomputable def weights : IntegerLookupTree := (.branch 1092 (.branch 884 (.leaf (99918596400000:ℤ)) (.leaf (21211824000000:ℤ))) (.branch 1768 (.leaf (40973842700000:ℤ)) (.branch 3048 (.leaf (12551566300000:ℤ)) (.leaf (1135884900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 150 (.branch 129 (.leaf (1803145047260848:ℤ)) (.leaf (2001095155197553:ℤ))) (.branch 181 (.leaf (2269284152883762:ℤ)) (.branch 200 (.leaf (2760261478936141:ℤ)) (.leaf (3135740220218651:ℤ))))), (.branch 150 (.branch 129 (.leaf (1812062296697467:ℤ)) (.leaf (2015064048815370:ℤ))) (.branch 181 (.leaf (2291915476819015:ℤ)) (.branch 200 (.leaf (2804109970103943:ℤ)) (.leaf (3200396102360764:ℤ))))), (.branch 150 (.branch 129 (.leaf (1805491432060956:ℤ)) (.leaf (2005071377320021:ℤ))) (.branch 181 (.leaf (2276378197925580:ℤ)) (.branch 200 (.leaf (2776298251603728:ℤ)) (.leaf (3161970368466053:ℤ))))), (.branch 150 (.branch 129 (.leaf (1814757391176664:ℤ)) (.leaf (2019640673499667:ℤ))) (.branch 181 (.leaf (2300105638658397:ℤ)) (.branch 200 (.leaf (2822736571865656:ℤ)) (.leaf (3231009754384150:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 21 7) 8000 (endpointMeanRuns 21 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 21 7, EndpointRunConditions (endpointMeanCutoff 21 7) (endpointMeanBox 21 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 21 7 h) (endpointMeanCornerA 21 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 7, endpointJoint24Q (endpointMeanCornerK 21 7 h) (endpointMeanCornerA 21 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 21 7, endpointRunWeightQ (endpointMeanCutoff 21 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 21 7) = (111502673/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 21 7 h = (logRoundedQ ((endpointMeanCutoff 21 7:ℚ)/200)).2+(111502673/250000000000000:ℚ)+((endpointMeanRuns 21 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 21 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 21 7) r*endpointJoint24Q (endpointMeanCornerK 21 7 h) (endpointMeanCornerA 21 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 21 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 21 7 h≤endpointMeanCorner 21 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 21 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint21_07

namespace EndpointAnalyticJoint21_08
private noncomputable def weights : IntegerLookupTree := (.branch 1092 (.branch 884 (.leaf (95581970800000:ℤ)) (.leaf (21030844800000:ℤ))) (.branch 1768 (.leaf (40674213000000:ℤ)) (.branch 3048 (.leaf (12476948500000:ℤ)) (.leaf (1130288900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 150 (.branch 129 (.leaf (1812062296697467:ℤ)) (.leaf (2015064048815370:ℤ))) (.branch 181 (.leaf (2291915476819015:ℤ)) (.branch 200 (.leaf (2804109970103943:ℤ)) (.leaf (3200396102360764:ℤ))))), (.branch 150 (.branch 129 (.leaf (1821023645380364:ℤ)) (.leaf (2029130454032475:ℤ))) (.branch 181 (.leaf (2314772500485350:ℤ)) (.branch 200 (.leaf (2848655022156412:ℤ)) (.leaf (3266385125261349:ℤ))))), (.branch 150 (.branch 129 (.leaf (1814757391176664:ℤ)) (.leaf (2019640673499667:ℤ))) (.branch 181 (.leaf (2300105638658397:ℤ)) (.branch 200 (.leaf (2822736571865656:ℤ)) (.leaf (3231009754384150:ℤ))))), (.branch 150 (.branch 129 (.leaf (1824070904103377:ℤ)) (.leaf (2034315833437366:ℤ))) (.branch 181 (.leaf (2324080398331557:ℤ)) (.branch 200 (.leaf (2869951652184793:ℤ)) (.leaf (3301556566448763:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 21 8) 8000 (endpointMeanRuns 21 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 21 8, EndpointRunConditions (endpointMeanCutoff 21 8) (endpointMeanBox 21 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 21 8 h) (endpointMeanCornerA 21 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 8, endpointJoint24Q (endpointMeanCornerK 21 8 h) (endpointMeanCornerA 21 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 21 8, endpointRunWeightQ (endpointMeanCutoff 21 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 21 8) = (27770633/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 21 8 h = (logRoundedQ ((endpointMeanCutoff 21 8:ℚ)/200)).2+(27770633/62500000000000:ℚ)+((endpointMeanRuns 21 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 21 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 21 8) r*endpointJoint24Q (endpointMeanCornerK 21 8 h) (endpointMeanCornerA 21 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 21 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 21 8 h≤endpointMeanCorner 21 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 21 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint21_08

namespace EndpointAnalyticJoint21_09
private noncomputable def weights : IntegerLookupTree := (.branch 1092 (.branch 884 (.leaf (92001456200000:ℤ)) (.leaf (20877795200000:ℤ))) (.branch 1768 (.leaf (40420823800000:ℤ)) (.branch 3048 (.leaf (12413846200000:ℤ)) (.leaf (1125556500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 150 (.branch 129 (.leaf (1821023645380364:ℤ)) (.leaf (2029130454032475:ℤ))) (.branch 181 (.leaf (2314772500485350:ℤ)) (.branch 200 (.leaf (2848655022156412:ℤ)) (.leaf (3266385125261349:ℤ))))), (.branch 150 (.branch 129 (.leaf (1830029311397363:ℤ)) (.leaf (2043295051540709:ℤ))) (.branch 181 (.leaf (2337857474761637:ℤ)) (.branch 200 (.leaf (2893907700401688:ℤ)) (.leaf (3333734776972901:ℤ))))), (.branch 150 (.branch 129 (.leaf (1824070904103377:ℤ)) (.leaf (2034315833437366:ℤ))) (.branch 181 (.leaf (2324080398331557:ℤ)) (.branch 200 (.leaf (2869951652184793:ℤ)) (.leaf (3301556566448763:ℤ))))), (.branch 150 (.branch 129 (.leaf (1833432214891919:ℤ)) (.leaf (2049097626362810:ℤ))) (.branch 181 (.leaf (2348305054831941:ℤ)) (.branch 200 (.leaf (2917956485197032:ℤ)) (.leaf (3373643718243316:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 21 9) 8000 (endpointMeanRuns 21 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 21 9, EndpointRunConditions (endpointMeanCutoff 21 9) (endpointMeanBox 21 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 21 9 h) (endpointMeanCornerA 21 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 9, endpointJoint24Q (endpointMeanCornerK 21 9 h) (endpointMeanCornerA 21 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 21 9, endpointRunWeightQ (endpointMeanCutoff 21 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 21 9) = (442908917/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 21 9 h = (logRoundedQ ((endpointMeanCutoff 21 9:ℚ)/200)).2+(442908917/1000000000000000:ℚ)+((endpointMeanRuns 21 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 21 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 21 9) r*endpointJoint24Q (endpointMeanCornerK 21 9 h) (endpointMeanCornerA 21 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 21 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 21 9 h≤endpointMeanCorner 21 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 21 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint21_09

namespace EndpointAnalyticJoint21_10
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 884 (.leaf (87977282200000:ℤ)) (.branch 1092 (.leaf (20701593200000:ℤ)) (.leaf (23780113200000:ℤ)))) (.branch 1768 (.leaf (7697962000000:ℤ)) (.branch 3048 (.leaf (12341198200000:ℤ)) (.leaf (1120108200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 160 (.branch 129 (.leaf (1830029311397363:ℤ)) (.branch 150 (.leaf (2043295051540709:ℤ)) (.leaf (2337857474761637:ℤ)))) (.branch 181 (.leaf (2499247724626619:ℤ)) (.branch 200 (.leaf (2893907700401688:ℤ)) (.leaf (3333734776972901:ℤ))))), (.branch 160 (.branch 129 (.leaf (1839079513914817:ℤ)) (.branch 150 (.leaf (2057558526783578:ℤ)) (.leaf (2361172672974493:ℤ)))) (.branch 181 (.leaf (2528405214755737:ℤ)) (.branch 200 (.leaf (2939879245927294:ℤ)) (.leaf (3402473112324540:ℤ))))), (.branch 160 (.branch 129 (.leaf (1833432214891919:ℤ)) (.branch 150 (.leaf (2049097626362810:ℤ)) (.leaf (2348305054831941:ℤ)))) (.branch 181 (.leaf (2512958091258984:ℤ)) (.branch 200 (.leaf (2917956485197032:ℤ)) (.leaf (3373643718243316:ℤ))))), (.branch 160 (.branch 129 (.leaf (1842841568845601:ℤ)) (.branch 150 (.leaf (2063986827095099:ℤ)) (.leaf (2372782212916601:ℤ)))) (.branch 181 (.leaf (2543666743410023:ℤ)) (.branch 200 (.leaf (2966764280862239:ℤ)) (.leaf (3447304841996014:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 21 10) 8000 (endpointMeanRuns 21 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 21 10, EndpointRunConditions (endpointMeanCutoff 21 10) (endpointMeanBox 21 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 21 10 h) (endpointMeanCornerA 21 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 10, endpointJoint24Q (endpointMeanCornerK 21 10 h) (endpointMeanCornerA 21 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 21 10, endpointRunWeightQ (endpointMeanCutoff 21 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 21 10) = (220636357/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 21 10 h = (logRoundedQ ((endpointMeanCutoff 21 10:ℚ)/200)).2+(220636357/500000000000000:ℚ)+((endpointMeanRuns 21 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 21 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 21 10) r*endpointJoint24Q (endpointMeanCornerK 21 10 h) (endpointMeanCornerA 21 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 21 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 21 10 h≤endpointMeanCorner 21 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 21 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint21_10

namespace EndpointAnalyticJoint21_11
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 884 (.leaf (84654327400000:ℤ)) (.branch 1092 (.leaf (20552531000000:ℤ)) (.leaf (23630322900000:ℤ)))) (.branch 1768 (.leaf (7655224400000:ℤ)) (.branch 3048 (.leaf (12279739800000:ℤ)) (.leaf (1115499000000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 160 (.branch 129 (.leaf (1839079513914817:ℤ)) (.branch 150 (.leaf (2057558526783578:ℤ)) (.leaf (2361172672974493:ℤ)))) (.branch 181 (.leaf (2528405214755737:ℤ)) (.branch 200 (.leaf (2939879245927294:ℤ)) (.leaf (3402473112324540:ℤ))))), (.branch 160 (.branch 129 (.leaf (1848174473182942:ℤ)) (.branch 150 (.leaf (2071921569989403:ℤ)) (.leaf (2384720391122197:ℤ)))) (.branch 181 (.leaf (2557902870936520:ℤ)) (.branch 200 (.leaf (2986581078392502:ℤ)) (.leaf (3472628764608390:ℤ))))), (.branch 160 (.branch 129 (.leaf (1842841568845601:ℤ)) (.branch 150 (.leaf (2063986827095099:ℤ)) (.leaf (2372782212916601:ℤ)))) (.branch 181 (.leaf (2543666743410023:ℤ)) (.branch 200 (.leaf (2966764280862239:ℤ)) (.leaf (3447304841996014:ℤ))))), (.branch 160 (.branch 129 (.leaf (1852299212526669:ℤ)) (.branch 150 (.leaf (2078984216083332:ℤ)) (.leaf (2397514504492831:ℤ)))) (.branch 181 (.leaf (2574750659008638:ℤ)) (.branch 200 (.leaf (3016388470099378:ℤ)) (.leaf (3522574304271003:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 21 11) 8000 (endpointMeanRuns 21 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 21 11, EndpointRunConditions (endpointMeanCutoff 21 11) (endpointMeanBox 21 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 21 11 h) (endpointMeanCornerA 21 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 11, endpointJoint24Q (endpointMeanCornerK 21 11 h) (endpointMeanCornerA 21 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 21 11, endpointRunWeightQ (endpointMeanCutoff 21 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 21 11) = (43988853/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 21 11 h = (logRoundedQ ((endpointMeanCutoff 21 11:ℚ)/200)).2+(43988853/100000000000000:ℚ)+((endpointMeanRuns 21 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 21 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 21 11) r*endpointJoint24Q (endpointMeanCornerK 21 11 h) (endpointMeanCornerA 21 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 21 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 21 11 h≤endpointMeanCorner 21 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 21 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint21_11

namespace EndpointAnalyticJoint21_12
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1092 (.branch 884 (.leaf (81443664100000:ℤ)) (.leaf (20405239900000:ℤ))) (.branch 1195 (.leaf (6515778300000:ℤ)) (.leaf (13774346000000:ℤ)))) (.branch 2389 (.branch 1768 (.leaf (7612994500000:ℤ)) (.leaf (7124583900000:ℤ))) (.branch 3048 (.leaf (1626334100000:ℤ)) (.leaf (1110944600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 160 (.branch 137 (.branch 129 (.leaf (1848174473182942:ℤ)) (.leaf (2071921569989403:ℤ))) (.branch 150 (.leaf (2183765198077009:ℤ)) (.leaf (2384720391122197:ℤ)))) (.branch 181 (.branch 174 (.leaf (2557902870936520:ℤ)) (.leaf (2832702413659967:ℤ))) (.branch 200 (.leaf (2986581078392502:ℤ)) (.leaf (3472628764608390:ℤ))))), (.branch 160 (.branch 137 (.branch 129 (.leaf (1857314410541170:ℤ)) (.leaf (2086384876204736:ℤ))) (.branch 150 (.leaf (2201314658432085:ℤ)) (.leaf (2408502948100750:ℤ)))) (.branch 181 (.branch 174 (.leaf (2587744661718469:ℤ)) (.leaf (2873412755857148:ℤ))) (.branch 200 (.leaf (3034024798865059:ℤ)) (.leaf (3544230957506935:ℤ))))), (.branch 160 (.branch 137 (.branch 129 (.leaf (1852299212526669:ℤ)) (.leaf (2078984216083332:ℤ))) (.branch 150 (.leaf (2192650919709388:ℤ)) (.leaf (2397514504492831:ℤ)))) (.branch 181 (.branch 174 (.leaf (2574750659008638:ℤ)) (.leaf (2857361609692756:ℤ))) (.branch 200 (.leaf (3016388470099378:ℤ)) (.leaf (3522574304271003:ℤ))))), (.branch 160 (.branch 137 (.branch 129 (.leaf (1861805393762728:ℤ)) (.leaf (2094090579447513:ℤ))) (.branch 150 (.leaf (2211019859298202:ℤ)) (.leaf (2422504588901149:ℤ)))) (.branch 181 (.branch 174 (.leaf (2606214423819593:ℤ)) (.leaf (2900520611363733:ℤ))) (.branch 200 (.leaf (3066842708482431:ℤ)) (.leaf (3599487222002013:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 21 12) 8000 (endpointMeanRuns 21 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 21 12, EndpointRunConditions (endpointMeanCutoff 21 12) (endpointMeanBox 21 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 21 12 h) (endpointMeanCornerA 21 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 12, endpointJoint24Q (endpointMeanCornerK 21 12 h) (endpointMeanCornerA 21 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 21 12, endpointRunWeightQ (endpointMeanCutoff 21 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 21 12) = (54815099/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 21 12 h = (logRoundedQ ((endpointMeanCutoff 21 12:ℚ)/200)).2+(54815099/125000000000000:ℚ)+((endpointMeanRuns 21 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 21 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 21 12) r*endpointJoint24Q (endpointMeanCornerK 21 12 h) (endpointMeanCornerA 21 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 21 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 21 12 h≤endpointMeanCorner 21 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 21 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint21_12

namespace EndpointAnalyticJoint21_13
private noncomputable def weights : IntegerLookupTree := (.branch 1195 (.branch 951 (.branch 884 (.leaf (77834573200000:ℤ)) (.leaf (6361110400000:ℤ))) (.branch 1092 (.leaf (11865620400000:ℤ)) (.leaf (6466426500000:ℤ)))) (.branch 1768 (.branch 1474 (.leaf (13677381100000:ℤ)) (.leaf (7564352100000:ℤ))) (.branch 2389 (.leaf (7083173900000:ℤ)) (.branch 3048 (.leaf (1617884300000:ℤ)) (.leaf (1105698700000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 160 (.branch 137 (.branch 129 (.leaf (1857314410541170:ℤ)) (.leaf (2086384876204736:ℤ))) (.branch 150 (.leaf (2201314658432085:ℤ)) (.leaf (2408502948100750:ℤ)))) (.branch 181 (.branch 174 (.leaf (2587744661718469:ℤ)) (.leaf (2873412755857148:ℤ))) (.branch 193 (.leaf (3034024798865059:ℤ)) (.branch 200 (.leaf (3342241812800508:ℤ)) (.leaf (3544230957506935:ℤ)))))), (.branch 160 (.branch 137 (.branch 129 (.leaf (1866499548423550:ℤ)) (.leaf (2100949145327987:ℤ))) (.branch 150 (.leaf (2219005152062628:ℤ)) (.leaf (2432522685932267:ℤ)))) (.branch 181 (.branch 174 (.leaf (2617934601950187:ℤ)) (.leaf (2914708169028892:ℤ))) (.branch 193 (.leaf (3082222192702977:ℤ)) (.branch 200 (.leaf (3404947812481986:ℤ)) (.leaf (3617309517266267:ℤ)))))), (.branch 160 (.branch 137 (.branch 129 (.leaf (1861805393762728:ℤ)) (.leaf (2094090579447513:ℤ))) (.branch 150 (.leaf (2211019859298202:ℤ)) (.leaf (2422504588901149:ℤ)))) (.branch 181 (.branch 174 (.leaf (2606214423819593:ℤ)) (.leaf (2900520611363733:ℤ))) (.branch 193 (.leaf (3066842708482431:ℤ)) (.branch 200 (.leaf (3387814114798354:ℤ)) (.leaf (3599487222002013:ℤ)))))), (.branch 160 (.branch 137 (.branch 129 (.leaf (1871360361653281:ℤ)) (.leaf (2109306709019792:ℤ))) (.branch 150 (.leaf (2229542684732951:ℤ)) (.leaf (2447755153201280:ℤ)))) (.branch 181 (.branch 174 (.leaf (2638062679646256:ℤ)) (.leaf (2944331507922259:ℤ))) (.branch 193 (.leaf (3118140879998117:ℤ)) (.branch 200 (.leaf (3454972569923483:ℤ)) (.leaf (3678079478876200:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 21 13) 8000 (endpointMeanRuns 21 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 21 13, EndpointRunConditions (endpointMeanCutoff 21 13) (endpointMeanBox 21 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 21 13 h) (endpointMeanCornerA 21 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 13, endpointJoint24Q (endpointMeanCornerK 21 13 h) (endpointMeanCornerA 21 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 21 13, endpointRunWeightQ (endpointMeanCutoff 21 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 21 13) = (436945369/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 21 13 h = (logRoundedQ ((endpointMeanCutoff 21 13:ℚ)/200)).2+(436945369/1000000000000000:ℚ)+((endpointMeanRuns 21 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 21 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 21 13) r*endpointJoint24Q (endpointMeanCornerK 21 13 h) (endpointMeanCornerA 21 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 21 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 21 13 h≤endpointMeanCorner 21 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 21 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint21_13

namespace EndpointAnalyticJoint21_14
private noncomputable def weights : IntegerLookupTree := (.branch 1340 (.branch 1028 (.branch 884 (.leaf (74853910700000:ℤ)) (.branch 951 (.leaf (6314308700000:ℤ)) (.leaf (6394944200000:ℤ)))) (.branch 1092 (.leaf (4549677600000:ℤ)) (.branch 1195 (.leaf (6424655800000:ℤ)) (.leaf (7225303800000:ℤ))))) (.branch 1965 (.branch 1474 (.leaf (4866757000000:ℤ)) (.branch 1768 (.leaf (7523182100000:ℤ)) (.leaf (2639604800000:ℤ)))) (.branch 2389 (.leaf (3222907000000:ℤ)) (.branch 3048 (.leaf (1610732500000:ℤ)) (.leaf (1101258600000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 145 (.branch 129 (.leaf (1866499548423550:ℤ)) (.branch 137 (.leaf (2100949145327987:ℤ)) (.leaf (2219005152062628:ℤ)))) (.branch 150 (.leaf (2346981730493400:ℤ)) (.branch 160 (.leaf (2432522685932267:ℤ)) (.leaf (2617934601950187:ℤ))))) (.branch 186 (.branch 174 (.leaf (2739364921437526:ℤ)) (.branch 181 (.leaf (2914708169028892:ℤ)) (.leaf (3082222192702977:ℤ)))) (.branch 193 (.leaf (3210856009823194:ℤ)) (.branch 200 (.leaf (3404947812481986:ℤ)) (.leaf (3617309517266267:ℤ)))))), (.branch 166 (.branch 145 (.branch 129 (.leaf (1875730110364151:ℤ)) (.branch 137 (.leaf (2115615082143290:ℤ)) (.leaf (2236837812358761:ℤ)))) (.branch 150 (.leaf (2368560259179983:ℤ)) (.branch 160 (.leaf (2456781969995580:ℤ)) (.leaf (2648476753319527:ℤ))))) (.branch 186 (.branch 174 (.leaf (2774362068088784:ℤ)) (.branch 181 (.leaf (2956597061555647:ℤ)) (.leaf (3131185232482094:ℤ)))) (.branch 193 (.leaf (3265566034846598:ℤ)) (.branch 200 (.leaf (3468830280718486:ℤ)) (.leaf (3691894885120362:ℤ)))))), (.branch 166 (.branch 145 (.branch 129 (.leaf (1871360361653281:ℤ)) (.branch 137 (.leaf (2109306709019792:ℤ)) (.leaf (2229542684732951:ℤ)))) (.branch 150 (.leaf (2360214553657689:ℤ)) (.branch 160 (.leaf (2447755153201280:ℤ)) (.leaf (2638062679646256:ℤ))))) (.branch 186 (.branch 174 (.leaf (2763126689125117:ℤ)) (.branch 181 (.leaf (2944331507922259:ℤ)) (.leaf (3118140879998117:ℤ)))) (.branch 193 (.leaf (3252080969940168:ℤ)) (.branch 200 (.leaf (3454972569923483:ℤ)) (.leaf (3678079478876200:ℤ)))))), (.branch 166 (.branch 145 (.branch 129 (.leaf (1880964366576214:ℤ)) (.branch 137 (.leaf (2124633402385936:ℤ)) (.leaf (2248220685192762:ℤ)))) (.branch 150 (.leaf (2382871515244025:ℤ)) (.branch 160 (.leaf (2473268912461035:ℤ)) (.leaf (2670300125015398:ℤ))))) (.branch 186 (.branch 174 (.leaf (2800154326869247:ℤ)) (.branch 181 (.leaf (2988804145910839:ℤ)) (.leaf (3170297100866508:ℤ)))) (.branch 193 (.leaf (3310508761689460:ℤ)) (.branch 200 (.leaf (3523462343102663:ℤ)) (.leaf (3758387742075624:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 21 14) 8000 (endpointMeanRuns 21 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 21 14, EndpointRunConditions (endpointMeanCutoff 21 14) (endpointMeanBox 21 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 21 14 h) (endpointMeanCornerA 21 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 14, endpointJoint24Q (endpointMeanCornerK 21 14 h) (endpointMeanCornerA 21 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 21 14, endpointRunWeightQ (endpointMeanCutoff 21 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 21 14) = (435611957/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 21 14 h = (logRoundedQ ((endpointMeanCutoff 21 14:ℚ)/200)).2+(435611957/1000000000000000:ℚ)+((endpointMeanRuns 21 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 21 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 21 14) r*endpointJoint24Q (endpointMeanCornerK 21 14 h) (endpointMeanCornerA 21 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 21 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 21 14 h≤endpointMeanCorner 21 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 21 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint21_14

namespace EndpointAnalyticJoint21_15
private noncomputable def weights : IntegerLookupTree := (.branch 1340 (.branch 1028 (.branch 884 (.leaf (71503043800000:ℤ)) (.branch 951 (.leaf (6260383200000:ℤ)) (.leaf (6342837800000:ℤ)))) (.branch 1195 (.branch 1092 (.leaf (4514122900000:ℤ)) (.leaf (6376527200000:ℤ))) (.branch 1263 (.leaf (3402902700000:ℤ)) (.leaf (3327212300000:ℤ))))) (.branch 1965 (.branch 1579 (.branch 1474 (.leaf (4834087000000:ℤ)) (.leaf (2837392000000:ℤ))) (.branch 1768 (.leaf (3910545500000:ℤ)) (.leaf (2624077500000:ℤ)))) (.branch 3048 (.branch 2389 (.leaf (3205021600000:ℤ)) (.leaf (1602492200000:ℤ))) (.branch 4209 (.leaf (452695800000:ℤ)) (.leaf (48255800000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 160 (.branch 137 (.branch 121 (.leaf (1875730110364151:ℤ)) (.branch 129 (.leaf (2003780308066139:ℤ)) (.leaf (2115615082143290:ℤ)))) (.branch 150 (.branch 145 (.leaf (2236837812358761:ℤ)) (.leaf (2368560259179983:ℤ))) (.branch 156 (.leaf (2456781969995580:ℤ)) (.leaf (2569220736253302:ℤ))))) (.branch 181 (.branch 170 (.branch 166 (.leaf (2648476753319527:ℤ)) (.leaf (2774362068088784:ℤ))) (.branch 174 (.leaf (2863311759228385:ℤ)) (.leaf (2956597061555647:ℤ)))) (.branch 193 (.branch 186 (.leaf (3131185232482094:ℤ)) (.leaf (3265566034846598:ℤ))) (.branch 200 (.leaf (3468830280718486:ℤ)) (.leaf (3691894885120362:ℤ)))))), (.branch 160 (.branch 137 (.branch 121 (.leaf (1885006321002506:ℤ)) (.branch 129 (.leaf (2015843907816053:ℤ)) (.leaf (2130383396354608:ℤ)))) (.branch 150 (.branch 145 (.leaf (2254813781818883:ℤ)) (.leaf (2390337184340739:ℤ))) (.branch 156 (.leaf (2481283189259200:ℤ)) (.leaf (2597396195502753:ℤ))))) (.branch 181 (.branch 170 (.branch 166 (.leaf (2679375224900068:ℤ)) (.leaf (2809806325770831:ℤ))) (.branch 174 (.leaf (2902127746157961:ℤ)) (.leaf (2999087962659370:ℤ)))) (.branch 193 (.branch 186 (.leaf (3180926080970172:ℤ)) (.leaf (3321208268237147:ℤ))) (.branch 200 (.leaf (3533911290011339:ℤ)) (.leaf (3768018129971542:ℤ)))))), (.branch 160 (.branch 137 (.branch 121 (.leaf (1880964366576214:ℤ)) (.branch 129 (.leaf (2010889740678719:ℤ)) (.leaf (2124633402385936:ℤ)))) (.branch 150 (.branch 145 (.leaf (2248220685192762:ℤ)) (.leaf (2382871515244025:ℤ))) (.branch 156 (.leaf (2473268912461035:ℤ)) (.leaf (2588735408487342:ℤ))))) (.branch 181 (.branch 170 (.branch 166 (.leaf (2670300125015398:ℤ)) (.leaf (2800154326869247:ℤ))) (.branch 174 (.leaf (2892135191729185:ℤ)) (.leaf (2988804145910839:ℤ)))) (.branch 193 (.branch 186 (.leaf (3170297100866508:ℤ)) (.leaf (3310508761689460:ℤ))) (.branch 200 (.leaf (3523462343102663:ℤ)) (.leaf (3758387742075624:ℤ)))))), (.branch 160 (.branch 137 (.branch 121 (.leaf (1890617660194400:ℤ)) (.branch 129 (.leaf (2023473859097751:ℤ)) (.leaf (2140071462927152:ℤ)))) (.branch 150 (.branch 145 (.leaf (2267055160656872:ℤ)) (.leaf (2405745973120064:ℤ))) (.branch 156 (.leaf (2499048610048288:ℤ)) (.leaf (2618445436995761:ℤ))))) (.branch 181 (.branch 170 (.branch 166 (.leaf (2702931515870344:ℤ)) (.leaf (2837678158277719:ℤ))) (.branch 174 (.leaf (2933299953701790:ℤ)) (.leaf (3033948520599014:ℤ)))) (.branch 193 (.branch 186 (.leaf (3223325723425500:ℤ)) (.leaf (3369986283405585:ℤ))) (.branch 200 (.leaf (3593309825767288:ℤ)) (.leaf (3840449479384339:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 21 15) 8000 (endpointMeanRuns 21 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 21 15, EndpointRunConditions (endpointMeanCutoff 21 15) (endpointMeanBox 21 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 21 15 h) (endpointMeanCornerA 21 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 15, endpointJoint24Q (endpointMeanCornerK 21 15 h) (endpointMeanCornerA 21 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 21 15, endpointRunWeightQ (endpointMeanCutoff 21 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 21 15) = (434075583/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 21 15 h = (logRoundedQ ((endpointMeanCutoff 21 15:ℚ)/200)).2+(434075583/1000000000000000:ℚ)+((endpointMeanRuns 21 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 21 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 21 15) r*endpointJoint24Q (endpointMeanCornerK 21 15 h) (endpointMeanCornerA 21 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 21 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 21 15 h≤endpointMeanCorner 21 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 21 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint21_15

namespace EndpointAnalyticJoint21_16
private noncomputable def weights : IntegerLookupTree := (.branch 1340 (.branch 1092 (.branch 951 (.branch 884 (.leaf (68735397300000:ℤ)) (.leaf (6214727300000:ℤ))) (.branch 1028 (.leaf (6298722000000:ℤ)) (.leaf (4484020600000:ℤ)))) (.branch 1195 (.branch 1134 (.leaf (2585763900000:ℤ)) (.leaf (3446243100000:ℤ))) (.branch 1263 (.leaf (3382035300000:ℤ)) (.leaf (3307422200000:ℤ))))) (.branch 1965 (.branch 1579 (.branch 1474 (.leaf (4806427200000:ℤ)) (.leaf (2821816700000:ℤ))) (.branch 1768 (.leaf (3889953200000:ℤ)) (.leaf (2610931400000:ℤ)))) (.branch 2389 (.branch 2156 (.leaf (1604442300000:ℤ)) (.leaf (1220462000000:ℤ))) (.branch 3048 (.leaf (1595515500000:ℤ)) (.branch 4209 (.leaf (450896100000:ℤ)) (.leaf (48083000000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 160 (.branch 141 (.branch 129 (.branch 121 (.leaf (1885006321002506:ℤ)) (.leaf (2015843907816053:ℤ))) (.branch 137 (.leaf (2130383396354608:ℤ)) (.leaf (2254813781818883:ℤ)))) (.branch 150 (.branch 145 (.leaf (2321106604692375:ℤ)) (.leaf (2390337184340739:ℤ))) (.branch 156 (.leaf (2481283189259200:ℤ)) (.leaf (2597396195502753:ℤ))))) (.branch 178 (.branch 170 (.branch 166 (.leaf (2679375224900068:ℤ)) (.leaf (2809806325770831:ℤ))) (.branch 174 (.leaf (2902127746157961:ℤ)) (.leaf (2999087962659370:ℤ)))) (.branch 186 (.branch 181 (.leaf (3101012441961626:ℤ)) (.leaf (3180926080970172:ℤ))) (.branch 193 (.leaf (3321208268237147:ℤ)) (.branch 200 (.leaf (3533911290011339:ℤ)) (.leaf (3768018129971542:ℤ))))))), (.branch 160 (.branch 141 (.branch 129 (.branch 121 (.leaf (1894328406089069:ℤ)) (.leaf (2027980135507440:ℤ))) (.branch 137 (.leaf (2145254802620096:ℤ)) (.leaf (2272934212122904:ℤ)))) (.branch 150 (.branch 145 (.leaf (2341072857210647:ℤ)) (.leaf (2412314330064860:ℤ))) (.branch 156 (.leaf (2506028756516551:ℤ)) (.leaf (2625880642023212:ℤ))))) (.branch 178 (.branch 170 (.branch 166 (.leaf (2710634173703909:ℤ)) (.leaf (2845703406614309:ℤ))) (.branch 174 (.leaf (2941469935250629:ℤ)) (.leaf (3042189524140215:ℤ)))) (.branch 186 (.branch 181 (.leaf (3148218360939662:ℤ)) (.leaf (3231457094148170:ℤ))) (.branch 193 (.leaf (3377798593965641:ℤ)) (.branch 200 (.leaf (3600213326978602:ℤ)) (.leaf (3845710961332359:ℤ))))))), (.branch 160 (.branch 141 (.branch 129 (.branch 121 (.leaf (1890617660194400:ℤ)) (.leaf (2023473859097751:ℤ))) (.branch 137 (.leaf (2140071462927152:ℤ)) (.leaf (2267055160656872:ℤ)))) (.branch 150 (.branch 145 (.leaf (2334846370363147:ℤ)) (.leaf (2405745973120064:ℤ))) (.branch 156 (.leaf (2499048610048288:ℤ)) (.leaf (2618445436995761:ℤ))))) (.branch 178 (.branch 170 (.branch 166 (.leaf (2702931515870344:ℤ)) (.leaf (2837678158277719:ℤ))) (.branch 174 (.leaf (2933299953701790:ℤ)) (.leaf (3033948520599014:ℤ)))) (.branch 186 (.branch 181 (.leaf (3139998209511520:ℤ)) (.leaf (3223325723425500:ℤ))) (.branch 193 (.leaf (3369986283405585:ℤ)) (.branch 200 (.leaf (3593309825767288:ℤ)) (.leaf (3840449479384339:ℤ))))))), (.branch 160 (.branch 141 (.branch 129 (.branch 121 (.leaf (1900320495462243:ℤ)) (.leaf (2036136728744748:ℤ))) (.branch 137 (.leaf (2155621699862189:ℤ)) (.leaf (2286047421995095:ℤ)))) (.branch 150 (.branch 145 (.leaf (2355799653825125:ℤ)) (.leaf (2428840015148999:ℤ))) (.branch 156 (.leaf (2525097017925933:ℤ)) (.leaf (2648496437312686:ℤ))))) (.branch 178 (.branch 170 (.branch 166 (.leaf (2735961666272639:ℤ)) (.leaf (2875704832658115:ℤ))) (.branch 174 (.leaf (2975050627990355:ℤ)) (.leaf (3079774778229834:ℤ)))) (.branch 186 (.branch 181 (.leaf (3190287758188322:ℤ)) (.leaf (3277241340080332:ℤ))) (.branch 193 (.leaf (3430532394829253:ℤ)) (.branch 200 (.leaf (3664541932520246:ℤ)) (.leaf (3924302976668941:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 21 16) 8000 (endpointMeanRuns 21 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 21 16, EndpointRunConditions (endpointMeanCutoff 21 16) (endpointMeanBox 21 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 21 16 h) (endpointMeanCornerA 21 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 16, endpointJoint24Q (endpointMeanCornerK 21 16 h) (endpointMeanCornerA 21 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 21 16, endpointRunWeightQ (endpointMeanCutoff 21 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 21 16) = (13524213/31250000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 21 16 h = (logRoundedQ ((endpointMeanCutoff 21 16:ℚ)/200)).2+(13524213/31250000000000:ℚ)+((endpointMeanRuns 21 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 21 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 21 16) r*endpointJoint24Q (endpointMeanCornerK 21 16 h) (endpointMeanCornerA 21 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 21 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 21 16 h≤endpointMeanCorner 21 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 21 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint21_16

namespace EndpointAnalyticJoint21_17
private noncomputable def weights : IntegerLookupTree := (.branch 1340 (.branch 1092 (.branch 951 (.branch 884 (.leaf (65623750100000:ℤ)) (.leaf (6162106100000:ℤ))) (.branch 1028 (.leaf (6247875800000:ℤ)) (.leaf (4449325800000:ℤ)))) (.branch 1195 (.branch 1134 (.leaf (2566332100000:ℤ)) (.leaf (3420994500000:ℤ))) (.branch 1263 (.leaf (3357984400000:ℤ)) (.leaf (3284612900000:ℤ))))) (.branch 1965 (.branch 1579 (.branch 1474 (.leaf (4774547400000:ℤ)) (.leaf (2803865100000:ℤ))) (.branch 1768 (.leaf (3866219300000:ℤ)) (.leaf (2595779700000:ℤ)))) (.branch 2389 (.branch 2156 (.leaf (1595529000000:ℤ)) (.leaf (1213949500000:ℤ))) (.branch 3048 (.leaf (1587474500000:ℤ)) (.branch 4209 (.leaf (448821900000:ℤ)) (.leaf (47883800000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 160 (.branch 141 (.branch 129 (.branch 121 (.leaf (1894328406089069:ℤ)) (.leaf (2027980135507440:ℤ))) (.branch 137 (.leaf (2145254802620096:ℤ)) (.leaf (2272934212122904:ℤ)))) (.branch 150 (.branch 145 (.leaf (2341072857210647:ℤ)) (.leaf (2412314330064860:ℤ))) (.branch 156 (.leaf (2506028756516551:ℤ)) (.leaf (2625880642023212:ℤ))))) (.branch 178 (.branch 170 (.branch 166 (.leaf (2710634173703909:ℤ)) (.leaf (2845703406614309:ℤ))) (.branch 174 (.leaf (2941469935250629:ℤ)) (.leaf (3042189524140215:ℤ)))) (.branch 186 (.branch 181 (.leaf (3148218360939662:ℤ)) (.leaf (3231457094148170:ℤ))) (.branch 193 (.leaf (3377798593965641:ℤ)) (.branch 200 (.leaf (3600213326978602:ℤ)) (.leaf (3845710961332359:ℤ))))))), (.branch 160 (.branch 141 (.branch 129 (.branch 121 (.leaf (1903696592490732:ℤ)) (.leaf (2040189428391019:ℤ))) (.branch 137 (.leaf (2160230020586656:ℤ)) (.leaf (2291200264206003:ℤ)))) (.branch 150 (.branch 145 (.leaf (2361210860237411:ℤ)) (.leaf (2434493537212508:ℤ))) (.branch 156 (.leaf (2531021108623584:ℤ)) (.leaf (2654677464335620:ℤ))))) (.branch 178 (.branch 170 (.branch 166 (.leaf (2742257805240964:ℤ)) (.leaf (2882059095726004:ℤ))) (.branch 174 (.leaf (2981345459874321:ℤ)) (.leaf (3085910522138168:ℤ)))) (.branch 186 (.branch 181 (.leaf (3196142883544187:ℤ)) (.leaf (3282790824279597:ℤ))) (.branch 193 (.leaf (3435353166651085:ℤ)) (.branch 200 (.leaf (3667759300124578:ℤ)) (.leaf (3925005742534348:ℤ))))))), (.branch 160 (.branch 141 (.branch 129 (.branch 121 (.leaf (1900320495462243:ℤ)) (.leaf (2036136728744748:ℤ))) (.branch 137 (.leaf (2155621699862189:ℤ)) (.leaf (2286047421995095:ℤ)))) (.branch 150 (.branch 145 (.leaf (2355799653825125:ℤ)) (.leaf (2428840015148999:ℤ))) (.branch 156 (.leaf (2525097017925933:ℤ)) (.leaf (2648496437312686:ℤ))))) (.branch 178 (.branch 170 (.branch 166 (.leaf (2735961666272639:ℤ)) (.leaf (2875704832658115:ℤ))) (.branch 174 (.leaf (2975050627990355:ℤ)) (.leaf (3079774778229834:ℤ)))) (.branch 186 (.branch 181 (.leaf (3190287758188322:ℤ)) (.leaf (3277241340080332:ℤ))) (.branch 193 (.leaf (3430532394829253:ℤ)) (.branch 200 (.leaf (3664541932520246:ℤ)) (.leaf (3924302976668941:ℤ))))))), (.branch 160 (.branch 141 (.branch 129 (.branch 121 (.leaf (1910073126632360:ℤ)) (.leaf (2048878842443741:ℤ))) (.branch 137 (.leaf (2171284928289764:ℤ)) (.leaf (2305198791059058:ℤ)))) (.branch 150 (.branch 145 (.leaf (2376940975392481:ℤ)) (.leaf (2452155749236521:ℤ))) (.branch 156 (.leaf (2551416936949958:ℤ)) (.leaf (2678892322654628:ℤ))))) (.branch 178 (.branch 170 (.branch 166 (.leaf (2769395449112230:ℤ)) (.leaf (2914241088422933:ℤ))) (.branch 174 (.leaf (3017395554087831:ℤ)) (.leaf (3126293218300200:ℤ)))) (.branch 186 (.branch 181 (.leaf (3241382733663920:ℤ)) (.leaf (3332058787319069:ℤ))) (.branch 193 (.leaf (3492166294540542:ℤ)) (.branch 200 (.leaf (3737186111507015:ℤ)) (.leaf (4009987355740847:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 21 17) 8000 (endpointMeanRuns 21 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 21 17, EndpointRunConditions (endpointMeanCutoff 21 17) (endpointMeanBox 21 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 21 17 h) (endpointMeanCornerA 21 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 17, endpointJoint24Q (endpointMeanCornerK 21 17 h) (endpointMeanCornerA 21 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 21 17, endpointRunWeightQ (endpointMeanCutoff 21 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 21 17) = (215637801/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 21 17 h = (logRoundedQ ((endpointMeanCutoff 21 17:ℚ)/200)).2+(215637801/500000000000000:ℚ)+((endpointMeanRuns 21 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 21 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 21 17) r*endpointJoint24Q (endpointMeanCornerK 21 17 h) (endpointMeanCornerA 21 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 21 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 21 17 h≤endpointMeanCorner 21 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 21 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint21_17

namespace EndpointAnalyticJoint21_18
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1092 (.branch 951 (.branch 884 (.leaf (63053493900000:ℤ)) (.leaf (6117541300000:ℤ))) (.branch 1028 (.leaf (6204814300000:ℤ)) (.leaf (4419942900000:ℤ)))) (.branch 1263 (.branch 1195 (.leaf (6249040500000:ℤ)) (.leaf (3337615700000:ℤ))) (.branch 1340 (.leaf (3265295700000:ℤ)) (.leaf (4747548500000:ℤ))))) (.branch 2156 (.branch 1768 (.branch 1579 (.leaf (2788662000000:ℤ)) (.leaf (3846119100000:ℤ))) (.branch 1965 (.leaf (2582947700000:ℤ)) (.leaf (1587980400000:ℤ)))) (.branch 3048 (.branch 2389 (.leaf (1208434000000:ℤ)) (.leaf (1580664500000:ℤ))) (.branch 4209 (.leaf (447065300000:ℤ)) (.leaf (47715100000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 160 (.branch 141 (.branch 129 (.branch 121 (.leaf (1903696592490732:ℤ)) (.leaf (2040189428391019:ℤ))) (.branch 137 (.leaf (2160230020586656:ℤ)) (.leaf (2291200264206003:ℤ)))) (.branch 150 (.branch 145 (.leaf (2361210860237411:ℤ)) (.leaf (2434493537212508:ℤ))) (.branch 156 (.leaf (2531021108623584:ℤ)) (.leaf (2654677464335620:ℤ))))) (.branch 181 (.branch 170 (.branch 166 (.leaf (2742257805240964:ℤ)) (.leaf (2882059095726004:ℤ))) (.branch 174 (.leaf (2981345459874321:ℤ)) (.leaf (3085910522138168:ℤ)))) (.branch 193 (.branch 186 (.leaf (3282790824279597:ℤ)) (.leaf (3435353166651085:ℤ))) (.branch 200 (.leaf (3667759300124578:ℤ)) (.leaf (3925005742534348:ℤ)))))), (.branch 160 (.branch 141 (.branch 129 (.branch 121 (.leaf (1913111108196315:ℤ)) (.leaf (2052472226349985:ℤ))) (.branch 137 (.leaf (2175309774924783:ℤ)) (.leaf (2309613108333028:ℤ)))) (.branch 150 (.branch 145 (.leaf (2381522091177462:ℤ)) (.leaf (2456876663569011:ℤ))) (.branch 156 (.leaf (2556262706738758:ℤ)) (.leaf (2683790088121266:ℤ))))) (.branch 181 (.branch 170 (.branch 166 (.leaf (2774250374084756:ℤ)) (.leaf (2918879252121153:ℤ))) (.branch 174 (.leaf (3021761550099239:ℤ)) (.leaf (3130259858920004:ℤ)))) (.branch 193 (.branch 186 (.leaf (3334940023028562:ℤ)) (.leaf (3493888416172309:ℤ))) (.branch 200 (.leaf (3736572547755108:ℤ)) (.leaf (4005935504209154:ℤ)))))), (.branch 160 (.branch 141 (.branch 129 (.branch 121 (.leaf (1910073126632360:ℤ)) (.leaf (2048878842443741:ℤ))) (.branch 137 (.leaf (2171284928289764:ℤ)) (.leaf (2305198791059058:ℤ)))) (.branch 150 (.branch 145 (.leaf (2376940975392481:ℤ)) (.leaf (2452155749236521:ℤ))) (.branch 156 (.leaf (2551416936949958:ℤ)) (.leaf (2678892322654628:ℤ))))) (.branch 181 (.branch 170 (.branch 166 (.leaf (2769395449112230:ℤ)) (.leaf (2914241088422933:ℤ))) (.branch 174 (.leaf (3017395554087831:ℤ)) (.leaf (3126293218300200:ℤ)))) (.branch 193 (.branch 186 (.leaf (3332058787319069:ℤ)) (.leaf (3492166294540542:ℤ))) (.branch 200 (.leaf (3737186111507015:ℤ)) (.leaf (4009987355740847:ℤ)))))), (.branch 160 (.branch 141 (.branch 129 (.branch 121 (.leaf (1919875809262197:ℤ)) (.leaf (2061700696102837:ℤ))) (.branch 137 (.leaf (2187061969231286:ℤ)) (.leaf (2324510600774204:ℤ)))) (.branch 150 (.branch 145 (.leaf (2398272022549144:ℤ)) (.leaf (2475695303523259:ℤ))) (.branch 156 (.leaf (2578011197170583:ℤ)) (.leaf (2709637051148744:ℤ))))) (.branch 181 (.branch 170 (.branch 166 (.leaf (2803237796826374:ℤ)) (.leaf (2953293754283637:ℤ))) (.branch 174 (.leaf (3060343190186041:ℤ)) (.leaf (3173514295875707:ℤ)))) (.branch 193 (.branch 186 (.leaf (3387793149795326:ℤ)) (.leaf (3554907526046556:ℤ))) (.branch 200 (.leaf (3811270354992390:ℤ)) (.leaf (4097542592608542:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 21 18) 8000 (endpointMeanRuns 21 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 21 18, EndpointRunConditions (endpointMeanCutoff 21 18) (endpointMeanBox 21 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 21 18 h) (endpointMeanCornerA 21 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 18, endpointJoint24Q (endpointMeanCornerK 21 18 h) (endpointMeanCornerA 21 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 21 18, endpointRunWeightQ (endpointMeanCutoff 21 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 21 18) = (430005921/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 21 18 h = (logRoundedQ ((endpointMeanCutoff 21 18:ℚ)/200)).2+(430005921/1000000000000000:ℚ)+((endpointMeanRuns 21 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 21 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 21 18) r*endpointJoint24Q (endpointMeanCornerK 21 18 h) (endpointMeanCornerA 21 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 21 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 21 18 h≤endpointMeanCorner 21 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 21 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint21_18

namespace EndpointAnalyticJoint21_19
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1028 (.branch 884 (.leaf (60163574100000:ℤ)) (.branch 951 (.leaf (6066162700000:ℤ)) (.leaf (6155168800000:ℤ)))) (.branch 1195 (.branch 1092 (.leaf (4386067400000:ℤ)) (.leaf (6203185000000:ℤ))) (.branch 1340 (.leaf (6989526600000:ℤ)) (.leaf (4716421600000:ℤ))))) (.branch 1965 (.branch 1579 (.leaf (2771134400000:ℤ)) (.branch 1768 (.leaf (3822945700000:ℤ)) (.leaf (2568153800000:ℤ)))) (.branch 3048 (.branch 2389 (.leaf (3140605000000:ℤ)) (.leaf (1572813400000:ℤ))) (.branch 4209 (.leaf (445040000000:ℤ)) (.leaf (47520600000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 160 (.branch 137 (.branch 121 (.leaf (1913111108196315:ℤ)) (.branch 129 (.leaf (2052472226349985:ℤ)) (.leaf (2175309774924783:ℤ)))) (.branch 150 (.branch 145 (.leaf (2309613108333028:ℤ)) (.leaf (2456876663569011:ℤ))) (.branch 156 (.leaf (2556262706738758:ℤ)) (.leaf (2683790088121266:ℤ))))) (.branch 181 (.branch 166 (.leaf (2774250374084756:ℤ)) (.branch 174 (.leaf (2918879252121153:ℤ)) (.leaf (3130259858920004:ℤ)))) (.branch 193 (.branch 186 (.leaf (3334940023028562:ℤ)) (.leaf (3493888416172309:ℤ))) (.branch 200 (.leaf (3736572547755108:ℤ)) (.leaf (4005935504209154:ℤ)))))), (.branch 160 (.branch 137 (.branch 121 (.leaf (1922572182322140:ℤ)) (.branch 129 (.leaf (2064828971915767:ℤ)) (.leaf (2190494795363613:ℤ)))) (.branch 150 (.branch 145 (.leaf (2328173924173457:ℤ)) (.leaf (2479465584000479:ℤ))) (.branch 156 (.leaf (2581756036565389:ℤ)) (.leaf (2713221976629303:ℤ))))) (.branch 181 (.branch 166 (.leaf (2806616184444811:ℤ)) (.branch 174 (.leaf (2956169809667681:ℤ)) (.leaf (3175246564691924:ℤ)))) (.branch 193 (.branch 186 (.leaf (3387917644627392:ℤ)) (.leaf (3553421052358102:ℤ))) (.branch 200 (.leaf (3806676846041361:ℤ)) (.leaf (4088533958047583:ℤ)))))), (.branch 160 (.branch 137 (.branch 121 (.leaf (1919875809262197:ℤ)) (.branch 129 (.leaf (2061700696102837:ℤ)) (.leaf (2187061969231286:ℤ)))) (.branch 150 (.branch 145 (.leaf (2324510600774204:ℤ)) (.leaf (2475695303523259:ℤ))) (.branch 156 (.leaf (2578011197170583:ℤ)) (.leaf (2709637051148744:ℤ))))) (.branch 181 (.branch 166 (.leaf (2803237796826374:ℤ)) (.branch 174 (.leaf (2953293754283637:ℤ)) (.leaf (3173514295875707:ℤ)))) (.branch 193 (.branch 186 (.leaf (3387793149795326:ℤ)) (.leaf (3554907526046556:ℤ))) (.branch 200 (.leaf (3811270354992390:ℤ)) (.leaf (4097542592608542:ℤ)))))), (.branch 160 (.branch 137 (.branch 121 (.leaf (1929728800220760:ℤ)) (.branch 129 (.leaf (2074602788733538:ℤ)) (.leaf (2202953649673883:ℤ)))) (.branch 150 (.branch 145 (.leaf (2343984195232569:ℤ)) (.leaf (2499460826578982:ℤ))) (.branch 156 (.leaf (2604882658136575:ℤ)) (.leaf (2740734626348264:ℤ))))) (.branch 181 (.branch 166 (.leaf (2837493702127310:ℤ)) (.branch 174 (.leaf (2992869750460724:ℤ)) (.leaf (3221448623940432:ℤ)))) (.branch 193 (.branch 186 (.leaf (3444459764479285:ℤ)) (.leaf (3618775983978480:ℤ))) (.branch 200 (.leaf (3886823210146820:ℤ)) (.leaf (4187009536128372:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 21 19) 8000 (endpointMeanRuns 21 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 21 19, EndpointRunConditions (endpointMeanCutoff 21 19) (endpointMeanBox 21 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 21 19 h) (endpointMeanCornerA 21 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 19, endpointJoint24Q (endpointMeanCornerK 21 19 h) (endpointMeanCornerA 21 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 21 19, endpointRunWeightQ (endpointMeanCutoff 21 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 21 19) = (428542111/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 21 19 h = (logRoundedQ ((endpointMeanCutoff 21 19:ℚ)/200)).2+(428542111/1000000000000000:ℚ)+((endpointMeanRuns 21 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 21 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 21 19) r*endpointJoint24Q (endpointMeanCornerK 21 19 h) (endpointMeanCornerA 21 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 21 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 21 19 h≤endpointMeanCorner 21 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 21 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint21_19

namespace EndpointAnalyticJoint21_20
private noncomputable def weights : IntegerLookupTree := (.branch 1340 (.branch 951 (.branch 884 (.leaf (57776318700000:ℤ)) (.leaf (6022638100000:ℤ))) (.branch 1092 (.leaf (11272490700000:ℤ)) (.branch 1195 (.leaf (6164339200000:ℤ)) (.leaf (6948171400000:ℤ))))) (.branch 1965 (.branch 1474 (.leaf (4690052900000:ℤ)) (.branch 1768 (.leaf (7266608100000:ℤ)) (.leaf (2555621300000:ℤ)))) (.branch 2389 (.leaf (3126169200000:ℤ)) (.branch 3048 (.leaf (1566162300000:ℤ)) (.leaf (1073587900000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 160 (.branch 137 (.branch 129 (.leaf (1922572182322140:ℤ)) (.leaf (2190494795363613:ℤ))) (.branch 145 (.leaf (2328173924173457:ℤ)) (.branch 150 (.leaf (2479465584000479:ℤ)) (.leaf (2581756036565389:ℤ))))) (.branch 181 (.branch 166 (.leaf (2806616184444811:ℤ)) (.branch 174 (.leaf (2956169809667681:ℤ)) (.leaf (3175246564691924:ℤ)))) (.branch 193 (.leaf (3387917644627392:ℤ)) (.branch 200 (.leaf (3806676846041361:ℤ)) (.leaf (4088533958047583:ℤ)))))), (.branch 160 (.branch 137 (.branch 129 (.leaf (1932080045117605:ℤ)) (.leaf (2205785816726264:ℤ))) (.branch 145 (.leaf (2346883900876982:ℤ)) (.branch 150 (.leaf (2502262190610834:ℤ)) (.leaf (2607503608596443:ℤ))))) (.branch 181 (.branch 166 (.leaf (2839359590745758:ℤ)) (.branch 174 (.leaf (2993936778042476:ℤ)) (.leaf (3220879799438246:ℤ)))) (.branch 193 (.leaf (3441736849094548:ℤ)) (.branch 200 (.leaf (3878096417234909:ℤ)) (.leaf (4172835510842380:ℤ)))))), (.branch 160 (.branch 137 (.branch 129 (.leaf (1929728800220760:ℤ)) (.leaf (2202953649673883:ℤ))) (.branch 145 (.leaf (2343984195232569:ℤ)) (.branch 150 (.leaf (2499460826578982:ℤ)) (.leaf (2604882658136575:ℤ))))) (.branch 181 (.branch 166 (.leaf (2837493702127310:ℤ)) (.branch 174 (.leaf (2992869750460724:ℤ)) (.leaf (3221448623940432:ℤ)))) (.branch 193 (.leaf (3444459764479285:ℤ)) (.branch 200 (.leaf (3886823210146820:ℤ)) (.leaf (4187009536128372:ℤ)))))), (.branch 160 (.branch 137 (.branch 129 (.leaf (1939632357695322:ℤ)) (.leaf (2218960802613759:ℤ))) (.branch 145 (.leaf (2363620929786316:ℤ)) (.branch 150 (.leaf (2523454487598736:ℤ)) (.leaf (2632034209202740:ℤ))))) (.branch 181 (.branch 166 (.leaf (2872168218738825:ℤ)) (.branch 174 (.leaf (3032976089910006:ℤ)) (.leaf (3270106975782210:ℤ)))) (.branch 193 (.leaf (3502074224878058:ℤ)) (.branch 200 (.leaf (3963873790046625:ℤ)) (.leaf (4278429927062568:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 21 20) 8000 (endpointMeanRuns 21 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 21 20, EndpointRunConditions (endpointMeanCutoff 21 20) (endpointMeanBox 21 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 21 20 h) (endpointMeanCornerA 21 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 20, endpointJoint24Q (endpointMeanCornerK 21 20 h) (endpointMeanCornerA 21 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 21 20, endpointRunWeightQ (endpointMeanCutoff 21 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 21 20) = (26706379/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 21 20 h = (logRoundedQ ((endpointMeanCutoff 21 20:ℚ)/200)).2+(26706379/62500000000000:ℚ)+((endpointMeanRuns 21 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 21 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 21 20) r*endpointJoint24Q (endpointMeanCornerK 21 20 h) (endpointMeanCornerA 21 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 21 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 21 20 h≤endpointMeanCorner 21 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 21 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint21_20

namespace EndpointAnalyticJoint21_21
private noncomputable def weights : IntegerLookupTree := (.branch 1195 (.branch 951 (.branch 884 (.leaf (55468987300000:ℤ)) (.leaf (5979577200000:ℤ))) (.branch 1092 (.leaf (11197032100000:ℤ)) (.leaf (6125907300000:ℤ)))) (.branch 1768 (.branch 1474 (.leaf (13008340700000:ℤ)) (.leaf (7228728800000:ℤ))) (.branch 2389 (.leaf (6797452500000:ℤ)) (.branch 3048 (.leaf (1559582200000:ℤ)) (.leaf (1069502700000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 160 (.branch 137 (.branch 129 (.leaf (1932080045117605:ℤ)) (.leaf (2205785816726264:ℤ))) (.branch 150 (.leaf (2346883900876982:ℤ)) (.leaf (2607503608596443:ℤ)))) (.branch 181 (.branch 174 (.leaf (2839359590745758:ℤ)) (.leaf (3220879799438246:ℤ))) (.branch 193 (.leaf (3441736849094548:ℤ)) (.branch 200 (.leaf (3878096417234909:ℤ)) (.leaf (4172835510842380:ℤ)))))), (.branch 160 (.branch 137 (.branch 129 (.leaf (1941634927970760:ℤ)) (.leaf (2221183578965359:ℤ))) (.branch 150 (.leaf (2365744237149701:ℤ)) (.leaf (2633507958361763:ℤ)))) (.branch 181 (.branch 174 (.leaf (2872484998213138:ℤ)) (.leaf (3267168854786526:ℤ))) (.branch 193 (.leaf (3496411005503665:ℤ)) (.branch 200 (.leaf (3950855938036937:ℤ)) (.leaf (4258875278820552:ℤ)))))), (.branch 160 (.branch 137 (.branch 129 (.leaf (1939632357695322:ℤ)) (.leaf (2218960802613759:ℤ))) (.branch 150 (.leaf (2363620929786316:ℤ)) (.leaf (2632034209202740:ℤ)))) (.branch 181 (.branch 174 (.leaf (2872168218738825:ℤ)) (.leaf (3270106975782210:ℤ))) (.branch 193 (.leaf (3502074224878058:ℤ)) (.branch 200 (.leaf (3963873790046625:ℤ)) (.leaf (4278429927062568:ℤ)))))), (.branch 160 (.branch 137 (.branch 129 (.leaf (1949586741198209:ℤ)) (.leaf (2235084267099848:ℤ))) (.branch 150 (.leaf (2383422171142078:ℤ)) (.leaf (2659468769840563:ℤ)))) (.branch 181 (.branch 174 (.leaf (2907266462141814:ℤ)) (.leaf (3319500287413925:ℤ))) (.branch 193 (.leaf (3560652385326772:ℤ)) (.branch 200 (.leaf (4042451784892245:ℤ)) (.leaf (4371846417553366:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 21 21) 8000 (endpointMeanRuns 21 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 21 21, EndpointRunConditions (endpointMeanCutoff 21 21) (endpointMeanBox 21 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 21 21 h) (endpointMeanCornerA 21 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 21 21, endpointJoint24Q (endpointMeanCornerK 21 21 h) (endpointMeanCornerA 21 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 21 21, endpointRunWeightQ (endpointMeanCutoff 21 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 21 21) = (13314851/31250000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 21 21 h = (logRoundedQ ((endpointMeanCutoff 21 21:ℚ)/200)).2+(13314851/31250000000000:ℚ)+((endpointMeanRuns 21 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 21 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 21 21) r*endpointJoint24Q (endpointMeanCornerK 21 21 h) (endpointMeanCornerA 21 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 21 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 21 21 h≤endpointMeanCorner 21 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 21 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint21_21

namespace EndpointAnalyticJoint22_05
private noncomputable def weights : IntegerLookupTree := (.branch 1329 (.branch 864 (.leaf (100422545700000:ℤ)) (.leaf (52027692400000:ℤ))) (.branch 2008 (.leaf (24085780000000:ℤ)) (.leaf (18978431200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 143 (.leaf (1784299153835084:ℤ)) (.leaf (2156495372222261:ℤ))) (.branch 200 (.leaf (2461801673180011:ℤ)) (.leaf (3080277436115947:ℤ)))), (.branch 165 (.branch 143 (.leaf (1786195960342738:ℤ)) (.leaf (2160721499781631:ℤ))) (.branch 200 (.leaf (2468650286986220:ℤ)) (.leaf (3094406198400057:ℤ)))), (.branch 165 (.branch 143 (.leaf (1786240146341096:ℤ)) (.leaf (2161558606031325:ℤ))) (.branch 200 (.leaf (2471002949609043:ℤ)) (.leaf (3103564991766274:ℤ)))), (.branch 165 (.branch 143 (.leaf (1788210182107273:ℤ)) (.leaf (2165980585416126:ℤ))) (.branch 200 (.leaf (2478215565247866:ℤ)) (.leaf (3118660271756472:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 22 5) 8000 (endpointMeanRuns 22 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 22 5, EndpointRunConditions (endpointMeanCutoff 22 5) (endpointMeanBox 22 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 22 5 h) (endpointMeanCornerA 22 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 5, endpointJoint24Q (endpointMeanCornerK 22 5 h) (endpointMeanCornerA 22 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 22 5, endpointRunWeightQ (endpointMeanCutoff 22 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 22 5) = (223491073/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 22 5 h = (logRoundedQ ((endpointMeanCutoff 22 5:ℚ)/200)).2+(223491073/500000000000000:ℚ)+((endpointMeanRuns 22 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 22 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 22 5) r*endpointJoint24Q (endpointMeanCornerK 22 5 h) (endpointMeanCornerA 22 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 22 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 22 5 h≤endpointMeanCorner 22 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 22 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint22_05

namespace EndpointAnalyticJoint22_06
private noncomputable def weights : IntegerLookupTree := (.branch 1329 (.branch 864 (.leaf (97875475300000:ℤ)) (.leaf (51779490400000:ℤ))) (.branch 2008 (.leaf (23992456500000:ℤ)) (.leaf (18916921800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 143 (.leaf (1786195960342738:ℤ)) (.leaf (2160721499781631:ℤ))) (.branch 200 (.leaf (2468650286986220:ℤ)) (.leaf (3094406198400057:ℤ)))), (.branch 165 (.branch 143 (.leaf (1795175692746001:ℤ)) (.leaf (2180779887092185:ℤ))) (.branch 200 (.leaf (2501232186951153:ℤ)) (.leaf (3161970368466053:ℤ)))), (.branch 165 (.branch 143 (.leaf (1788210182107273:ℤ)) (.leaf (2165980585416126:ℤ))) (.branch 200 (.leaf (2478215565247866:ℤ)) (.leaf (3118660271756472:ℤ)))), (.branch 165 (.branch 143 (.leaf (1797537653771089:ℤ)) (.leaf (2186973700118722:ℤ))) (.branch 200 (.leaf (2512542611117962:ℤ)) (.leaf (3190903464613988:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 22 6) 8000 (endpointMeanRuns 22 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 22 6, EndpointRunConditions (endpointMeanCutoff 22 6) (endpointMeanBox 22 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 22 6 h) (endpointMeanCornerA 22 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 6, endpointJoint24Q (endpointMeanCornerK 22 6 h) (endpointMeanCornerA 22 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 22 6, endpointRunWeightQ (endpointMeanCutoff 22 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 22 6) = (111502673/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 22 6 h = (logRoundedQ ((endpointMeanCutoff 22 6:ℚ)/200)).2+(111502673/250000000000000:ℚ)+((endpointMeanRuns 22 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 22 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 22 6) r*endpointJoint24Q (endpointMeanCornerK 22 6 h) (endpointMeanCornerA 22 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 22 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 22 6 h≤endpointMeanCorner 22 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 22 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint22_06

namespace EndpointAnalyticJoint22_07
private noncomputable def weights : IntegerLookupTree := (.branch 1329 (.branch 864 (.leaf (93557419300000:ℤ)) (.leaf (51350114000000:ℤ))) (.branch 2008 (.leaf (23831011800000:ℤ)) (.leaf (18810513700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 143 (.leaf (1795175692746001:ℤ)) (.leaf (2180779887092185:ℤ))) (.branch 200 (.leaf (2501232186951153:ℤ)) (.leaf (3161970368466053:ℤ)))), (.branch 165 (.branch 143 (.leaf (1804200568904944:ℤ)) (.leaf (2201024480214798:ℤ))) (.branch 200 (.leaf (2534244111456592:ℤ)) (.leaf (3231009754384150:ℤ)))), (.branch 165 (.branch 143 (.leaf (1797537653771089:ℤ)) (.leaf (2186973700118722:ℤ))) (.branch 200 (.leaf (2512542611117962:ℤ)) (.leaf (3190903464613988:ℤ)))), (.branch 165 (.branch 143 (.leaf (1806913778400033:ℤ)) (.leaf (2208170284265083:ℤ))) (.branch 200 (.leaf (2547345138659105:ℤ)) (.leaf (3264820157775953:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 22 7) 8000 (endpointMeanRuns 22 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 22 7, EndpointRunConditions (endpointMeanCutoff 22 7) (endpointMeanBox 22 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 22 7 h) (endpointMeanCornerA 22 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 7, endpointJoint24Q (endpointMeanCornerK 22 7 h) (endpointMeanCornerA 22 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 22 7, endpointRunWeightQ (endpointMeanCutoff 22 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 22 7) = (27770633/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 22 7 h = (logRoundedQ ((endpointMeanCutoff 22 7:ℚ)/200)).2+(27770633/62500000000000:ℚ)+((endpointMeanRuns 22 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 22 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 22 7) r*endpointJoint24Q (endpointMeanCornerK 22 7 h) (endpointMeanCornerA 22 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 22 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 22 7 h≤endpointMeanCorner 22 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 22 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint22_07

namespace EndpointAnalyticJoint22_08
private noncomputable def weights : IntegerLookupTree := (.branch 1080 (.branch 864 (.leaf (89992608500000:ℤ)) (.leaf (23683114800000:ℤ))) (.branch 1329 (.leaf (17082009500000:ℤ)) (.branch 2008 (.leaf (23694482100000:ℤ)) (.leaf (18720527100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 143 (.leaf (1804200568904944:ℤ)) (.leaf (2201024480214798:ℤ))) (.branch 180 (.leaf (2534244111456592:ℤ)) (.branch 200 (.leaf (2803366419905370:ℤ)) (.leaf (3231009754384150:ℤ))))), (.branch 165 (.branch 143 (.leaf (1813270815770505:ℤ)) (.leaf (2221457007733326:ℤ))) (.branch 180 (.leaf (2567691736080251:ℤ)) (.branch 200 (.leaf (2849585688645652:ℤ)) (.leaf (3301556566448763:ℤ))))), (.branch 165 (.branch 143 (.leaf (1806913778400033:ℤ)) (.leaf (2208170284265083:ℤ))) (.branch 180 (.leaf (2547345138659105:ℤ)) (.branch 200 (.leaf (2823031200908344:ℤ)) (.leaf (3264820157775953:ℤ))))), (.branch 165 (.branch 143 (.leaf (1816338809772533:ℤ)) (.leaf (2229572309921524:ℤ))) (.branch 180 (.leaf (2582629734013900:ℤ)) (.branch 200 (.leaf (2872083147380952:ℤ)) (.leaf (3340449117569792:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 22 8) 8000 (endpointMeanRuns 22 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 22 8, EndpointRunConditions (endpointMeanCutoff 22 8) (endpointMeanBox 22 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 22 8 h) (endpointMeanCornerA 22 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 8, endpointJoint24Q (endpointMeanCornerK 22 8 h) (endpointMeanCornerA 22 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 22 8, endpointRunWeightQ (endpointMeanCutoff 22 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 22 8) = (442908917/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 22 8 h = (logRoundedQ ((endpointMeanCutoff 22 8:ℚ)/200)).2+(442908917/1000000000000000:ℚ)+((endpointMeanRuns 22 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 22 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 22 8) r*endpointJoint24Q (endpointMeanCornerK 22 8 h) (endpointMeanCornerA 22 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 22 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 22 8 h≤endpointMeanCorner 22 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 22 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint22_08

namespace EndpointAnalyticJoint22_09
private noncomputable def weights : IntegerLookupTree := (.branch 1080 (.branch 864 (.leaf (85986514000000:ℤ)) (.leaf (23481075000000:ℤ))) (.branch 1329 (.leaf (16952957100000:ℤ)) (.branch 2008 (.leaf (23537299000000:ℤ)) (.leaf (18616927800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 143 (.leaf (1813270815770505:ℤ)) (.leaf (2221457007733326:ℤ))) (.branch 180 (.leaf (2567691736080251:ℤ)) (.branch 200 (.leaf (2849585688645652:ℤ)) (.leaf (3301556566448763:ℤ))))), (.branch 165 (.branch 143 (.leaf (1822386661434569:ℤ)) (.leaf (2242079214278391:ℤ))) (.branch 180 (.leaf (2601580811307627:ℤ)) (.branch 200 (.leaf (2896566977215994:ℤ)) (.leaf (3373643718243316:ℤ))))), (.branch 165 (.branch 143 (.leaf (1816338809772533:ℤ)) (.leaf (2229572309921524:ℤ))) (.branch 180 (.leaf (2582629734013900:ℤ)) (.branch 200 (.leaf (2872083147380952:ℤ)) (.leaf (3340449117569792:ℤ))))), (.branch 165 (.branch 143 (.leaf (1825813002990732:ℤ)) (.leaf (2251181768268045:ℤ))) (.branch 180 (.leaf (2618403074553029:ℤ)) (.branch 200 (.leaf (2921987402340968:ℤ)) (.leaf (3417830008337799:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 22 9) 8000 (endpointMeanRuns 22 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 22 9, EndpointRunConditions (endpointMeanCutoff 22 9) (endpointMeanBox 22 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 22 9 h) (endpointMeanCornerA 22 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 9, endpointJoint24Q (endpointMeanCornerK 22 9 h) (endpointMeanCornerA 22 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 22 9, endpointRunWeightQ (endpointMeanCutoff 22 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 22 9) = (220636357/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 22 9 h = (logRoundedQ ((endpointMeanCutoff 22 9:ℚ)/200)).2+(220636357/500000000000000:ℚ)+((endpointMeanRuns 22 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 22 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 22 9) r*endpointJoint24Q (endpointMeanCornerK 22 9 h) (endpointMeanCornerA 22 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 22 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 22 9 h≤endpointMeanCorner 22 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 22 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint22_09

namespace EndpointAnalyticJoint22_10
private noncomputable def weights : IntegerLookupTree := (.branch 1080 (.branch 864 (.leaf (82678853900000:ℤ)) (.leaf (23310154700000:ℤ))) (.branch 1329 (.leaf (16843782200000:ℤ)) (.branch 2008 (.leaf (23404326300000:ℤ)) (.leaf (18529285600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 143 (.leaf (1822386661434569:ℤ)) (.leaf (2242079214278391:ℤ))) (.branch 180 (.leaf (2601580811307627:ℤ)) (.branch 200 (.leaf (2896566977215994:ℤ)) (.leaf (3373643718243316:ℤ))))), (.branch 165 (.branch 143 (.leaf (1831548335135711:ℤ)) (.leaf (2262892860676355:ℤ))) (.branch 180 (.leaf (2635917163520639:ℤ)) (.branch 200 (.leaf (2944322849082609:ℤ)) (.leaf (3447304841996014:ℤ))))), (.branch 165 (.branch 143 (.leaf (1825813002990732:ℤ)) (.leaf (2251181768268045:ℤ))) (.branch 180 (.leaf (2618403074553029:ℤ)) (.branch 200 (.leaf (2921987402340968:ℤ)) (.leaf (3417830008337799:ℤ))))), (.branch 165 (.branch 143 (.leaf (1835336614487426:ℤ)) (.leaf (2273000669783530:ℤ))) (.branch 180 (.leaf (2654671930138880:ℤ)) (.branch 200 (.leaf (2972758775185574:ℤ)) (.leaf (3497003413239475:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 22 10) 8000 (endpointMeanRuns 22 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 22 10, EndpointRunConditions (endpointMeanCutoff 22 10) (endpointMeanBox 22 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 22 10 h) (endpointMeanCornerA 22 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 10, endpointJoint24Q (endpointMeanCornerK 22 10 h) (endpointMeanCornerA 22 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 22 10, endpointRunWeightQ (endpointMeanCutoff 22 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 22 10) = (43988853/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 22 10 h = (logRoundedQ ((endpointMeanCutoff 22 10:ℚ)/200)).2+(43988853/100000000000000:ℚ)+((endpointMeanRuns 22 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 22 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 22 10) r*endpointJoint24Q (endpointMeanCornerK 22 10 h) (endpointMeanCornerA 22 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 22 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 22 10 h≤endpointMeanCorner 22 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 22 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint22_10

namespace EndpointAnalyticJoint22_11
private noncomputable def weights : IntegerLookupTree := (.branch 1329 (.branch 864 (.leaf (78961333200000:ℤ)) (.branch 1080 (.leaf (23113310900000:ℤ)) (.leaf (16718048700000:ℤ)))) (.branch 2008 (.leaf (23251185600000:ℤ)) (.branch 3198 (.leaf (6571736600000:ℤ)) (.leaf (812570400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 127 (.leaf (1831548335135711:ℤ)) (.branch 143 (.leaf (2037623218085970:ℤ)) (.leaf (2262892860676355:ℤ)))) (.branch 180 (.leaf (2635917163520639:ℤ)) (.branch 200 (.leaf (2944322849082609:ℤ)) (.leaf (3447304841996014:ℤ))))), (.branch 165 (.branch 127 (.leaf (1840756067264942:ℤ)) (.branch 143 (.leaf (2051896334248372:ℤ)) (.leaf (2283899724099672:ℤ)))) (.branch 180 (.leaf (2670706695999351:ℤ)) (.branch 200 (.leaf (2992866074846328:ℤ)) (.leaf (3522574304271003:ℤ))))), (.branch 165 (.branch 127 (.leaf (1835336614487426:ℤ)) (.branch 143 (.leaf (2043977391954185:ℤ)) (.leaf (2273000669783530:ℤ)))) (.branch 180 (.leaf (2654671930138880:ℤ)) (.branch 200 (.leaf (2972758775185574:ℤ)) (.leaf (3497003413239475:ℤ))))), (.branch 165 (.branch 127 (.leaf (1844909902032973:ℤ)) (.branch 143 (.leaf (2058877704761288:ℤ)) (.leaf (2295031044432833:ℤ)))) (.branch 180 (.leaf (2691443164406726:ℤ)) (.branch 200 (.leaf (3024412332634555:ℤ)) (.leaf (3578010855535771:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 22 11) 8000 (endpointMeanRuns 22 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 22 11, EndpointRunConditions (endpointMeanCutoff 22 11) (endpointMeanBox 22 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 22 11 h) (endpointMeanCornerA 22 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 11, endpointJoint24Q (endpointMeanCornerK 22 11 h) (endpointMeanCornerA 22 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 22 11, endpointRunWeightQ (endpointMeanCutoff 22 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 22 11) = (438294407/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 22 11 h = (logRoundedQ ((endpointMeanCutoff 22 11:ℚ)/200)).2+(438294407/1000000000000000:ℚ)+((endpointMeanRuns 22 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 22 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 22 11) r*endpointJoint24Q (endpointMeanCornerK 22 11 h) (endpointMeanCornerA 22 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 22 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 22 11 h≤endpointMeanCorner 22 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 22 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint22_11

namespace EndpointAnalyticJoint22_12
private noncomputable def weights : IntegerLookupTree := (.branch 1329 (.branch 864 (.leaf (75891620600000:ℤ)) (.branch 1080 (.leaf (22946730400000:ℤ)) (.leaf (16611645800000:ℤ)))) (.branch 2008 (.branch 1727 (.leaf (14582716600000:ℤ)) (.leaf (4214013700000:ℤ))) (.branch 3198 (.leaf (6540929800000:ℤ)) (.leaf (809332100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 150 (.branch 127 (.leaf (1840756067264942:ℤ)) (.branch 143 (.leaf (2051896334248372:ℤ)) (.leaf (2283899724099672:ℤ)))) (.branch 180 (.branch 165 (.leaf (2397514504492831:ℤ)) (.leaf (2670706695999351:ℤ))) (.branch 200 (.leaf (2992866074846328:ℤ)) (.leaf (3522574304271003:ℤ))))), (.branch 150 (.branch 127 (.leaf (1850010089371532:ℤ)) (.branch 143 (.leaf (2066269430546048:ℤ)) (.leaf (2305101598218608:ℤ)))) (.branch 180 (.branch 165 (.leaf (2422504588901149:ℤ)) (.leaf (2705955389936862:ℤ))) (.branch 200 (.leaf (3042209635657644:ℤ)) (.leaf (3599487222002013:ℤ))))), (.branch 150 (.branch 127 (.leaf (1844909902032973:ℤ)) (.branch 143 (.leaf (2058877704761288:ℤ)) (.leaf (2295031044432833:ℤ)))) (.branch 180 (.branch 165 (.leaf (2411105717739668:ℤ)) (.leaf (2691443164406726:ℤ))) (.branch 200 (.leaf (3024412332634555:ℤ)) (.leaf (3578010855535771:ℤ))))), (.branch 150 (.branch 127 (.leaf (1854533124742303:ℤ)) (.branch 143 (.leaf (2073886638790241:ℤ)) (.leaf (2317274941855644:ℤ)))) (.branch 180 (.branch 165 (.leaf (2437385382416692:ℤ)) (.leaf (2728723736063579:ℤ))) (.branch 200 (.leaf (3076963403201454:ℤ)) (.leaf (3660894820366343:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 22 12) 8000 (endpointMeanRuns 22 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 22 12, EndpointRunConditions (endpointMeanCutoff 22 12) (endpointMeanBox 22 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 22 12 h) (endpointMeanCornerA 22 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 12, endpointJoint24Q (endpointMeanCornerK 22 12 h) (endpointMeanCornerA 22 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 22 12, endpointRunWeightQ (endpointMeanCutoff 22 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 22 12) = (436945369/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 22 12 h = (logRoundedQ ((endpointMeanCutoff 22 12:ℚ)/200)).2+(436945369/1000000000000000:ℚ)+((endpointMeanRuns 22 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 22 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 22 12) r*endpointJoint24Q (endpointMeanCornerK 22 12 h) (endpointMeanCornerA 22 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 22 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 22 12 h≤endpointMeanCorner 22 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 22 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint22_12

namespace EndpointAnalyticJoint22_13
private noncomputable def weights : IntegerLookupTree := (.branch 1329 (.branch 939 (.branch 864 (.leaf (72441204600000:ℤ)) (.leaf (7716870500000:ℤ))) (.branch 1080 (.leaf (12650608500000:ℤ)) (.leaf (16489064900000:ℤ)))) (.branch 1727 (.branch 1464 (.leaf (5269799100000:ℤ)) (.leaf (7281752000000:ℤ))) (.branch 2008 (.leaf (4188998200000:ℤ)) (.branch 3198 (.leaf (6505439000000:ℤ)) (.leaf (805601400000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 159 (.branch 143 (.branch 127 (.leaf (1850010089371532:ℤ)) (.leaf (2066269430546048:ℤ))) (.branch 150 (.leaf (2305101598218608:ℤ)) (.leaf (2422504588901149:ℤ)))) (.branch 180 (.branch 165 (.leaf (2586926526603805:ℤ)) (.leaf (2705955389936862:ℤ))) (.branch 192 (.leaf (3042209635657644:ℤ)) (.branch 200 (.leaf (3359144757359098:ℤ)) (.leaf (3599487222002013:ℤ)))))), (.branch 159 (.branch 143 (.branch 127 (.leaf (1859310634168817:ℤ)) (.leaf (2080743207318528:ℤ))) (.branch 150 (.leaf (2326500293354437:ℤ)) (.leaf (2447755153201280:ℤ)))) (.branch 180 (.branch 165 (.leaf (2618050013907548:ℤ)) (.leaf (2741669305467658:ℤ))) (.branch 192 (.leaf (3092366726688035:ℤ)) (.branch 200 (.leaf (3424813089351712:ℤ)) (.leaf (3678079478876200:ℤ)))))), (.branch 159 (.branch 143 (.branch 127 (.leaf (1854533124742303:ℤ)) (.leaf (2073886638790241:ℤ))) (.branch 150 (.leaf (2317274941855644:ℤ)) (.leaf (2437385382416692:ℤ)))) (.branch 180 (.branch 165 (.leaf (2606144297537089:ℤ)) (.leaf (2728723736063579:ℤ))) (.branch 192 (.leaf (3076963403201454:ℤ)) (.branch 200 (.leaf (3407978531708418:ℤ)) (.leaf (3660894820366343:ℤ)))))), (.branch 159 (.branch 143 (.branch 127 (.leaf (1864206543081888:ℤ)) (.leaf (2089004985874745:ℤ))) (.branch 150 (.leaf (2339734431557158:ℤ)) (.leaf (2463951480314146:ℤ)))) (.branch 180 (.branch 165 (.leaf (2639001041475620:ℤ)) (.leaf (2766520700205121:ℤ))) (.branch 192 (.leaf (3130427581742396:ℤ)) (.branch 200 (.leaf (3478461247307574:ℤ)) (.leaf (3745698777031313:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 22 13) 8000 (endpointMeanRuns 22 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 22 13, EndpointRunConditions (endpointMeanCutoff 22 13) (endpointMeanBox 22 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 22 13 h) (endpointMeanCornerA 22 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 13, endpointJoint24Q (endpointMeanCornerK 22 13 h) (endpointMeanCornerA 22 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 22 13, endpointRunWeightQ (endpointMeanCutoff 22 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 22 13) = (87078243/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 22 13 h = (logRoundedQ ((endpointMeanCutoff 22 13:ℚ)/200)).2+(87078243/200000000000000:ℚ)+((endpointMeanRuns 22 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 22 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 22 13) r*endpointJoint24Q (endpointMeanCornerK 22 13 h) (endpointMeanCornerA 22 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 22 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 22 13 h≤endpointMeanCorner 22 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 22 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint22_13

namespace EndpointAnalyticJoint22_14
private noncomputable def weights : IntegerLookupTree := (.branch 1329 (.branch 939 (.branch 864 (.leaf (69126337900000:ℤ)) (.leaf (7650234100000:ℤ))) (.branch 1080 (.leaf (12548504100000:ℤ)) (.branch 1152 (.leaf (4797997100000:ℤ)) (.leaf (10030448100000:ℤ))))) (.branch 2008 (.branch 1464 (.leaf (5234321500000:ℤ)) (.branch 1727 (.leaf (7235608700000:ℤ)) (.leaf (4164315900000:ℤ)))) (.branch 2467 (.leaf (3221187600000:ℤ)) (.branch 3198 (.leaf (1484831600000:ℤ)) (.leaf (801920400000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 159 (.branch 135 (.branch 127 (.leaf (1859310634168817:ℤ)) (.leaf (2080743207318528:ℤ))) (.branch 143 (.leaf (2198552041260732:ℤ)) (.branch 150 (.leaf (2326500293354437:ℤ)) (.leaf (2447755153201280:ℤ))))) (.branch 180 (.branch 165 (.leaf (2618050013907548:ℤ)) (.branch 175 (.leaf (2741669305467658:ℤ)) (.leaf (2968244388625727:ℤ)))) (.branch 192 (.leaf (3092366726688035:ℤ)) (.branch 200 (.leaf (3424813089351712:ℤ)) (.leaf (3678079478876200:ℤ)))))), (.branch 159 (.branch 135 (.branch 127 (.leaf (1868657935540033:ℤ)) (.leaf (2095318369811073:ℤ))) (.branch 143 (.leaf (2216337482110219:ℤ)) (.branch 150 (.leaf (2348097636633955:ℤ)) (.leaf (2473268912461035:ℤ))))) (.branch 180 (.branch 165 (.leaf (2649547949983607:ℤ)) (.branch 175 (.leaf (2777854582709472:ℤ)) (.leaf (3013743076834684:ℤ)))) (.branch 192 (.leaf (3143350760658566:ℤ)) (.branch 200 (.leaf (3491765179603695:ℤ)) (.leaf (3758387742075624:ℤ)))))), (.branch 159 (.branch 135 (.branch 127 (.leaf (1864206543081888:ℤ)) (.leaf (2089004985874745:ℤ))) (.branch 143 (.leaf (2209029071722778:ℤ)) (.branch 150 (.leaf (2339734431557158:ℤ)) (.leaf (2463951480314146:ℤ))))) (.branch 180 (.branch 165 (.leaf (2639001041475620:ℤ)) (.branch 175 (.leaf (2766520700205121:ℤ)) (.leaf (3001259725732435:ℤ)))) (.branch 192 (.leaf (3130427581742396:ℤ)) (.branch 200 (.leaf (3478461247307574:ℤ)) (.leaf (3745698777031313:ℤ)))))), (.branch 159 (.branch 135 (.branch 127 (.leaf (1873930418876848:ℤ)) (.leaf (2104233543620862:ℤ))) (.branch 143 (.leaf (2227655604090292:ℤ)) (.branch 150 (.leaf (2362411603100620:ℤ)) (.leaf (2490807133389288:ℤ))))) (.branch 180 (.branch 165 (.leaf (2672272024036043:ℤ)) (.branch 175 (.leaf (2804841209650803:ℤ)) (.leaf (3049673094111640:ℤ)))) (.branch 192 (.leaf (3184820734083965:ℤ)) (.branch 200 (.leaf (3550401663755495:ℤ)) (.leaf (3832467201789173:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 22 14) 8000 (endpointMeanRuns 22 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 22 14, EndpointRunConditions (endpointMeanCutoff 22 14) (endpointMeanBox 22 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 22 14 h) (endpointMeanCornerA 22 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 14, endpointJoint24Q (endpointMeanCornerK 22 14 h) (endpointMeanCornerA 22 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 22 14, endpointRunWeightQ (endpointMeanCutoff 22 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 22 14) = (86771553/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 22 14 h = (logRoundedQ ((endpointMeanCutoff 22 14:ℚ)/200)).2+(86771553/200000000000000:ℚ)+((endpointMeanRuns 22 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 22 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 22 14) r*endpointJoint24Q (endpointMeanCornerK 22 14 h) (endpointMeanCornerA 22 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 22 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 22 14 h≤endpointMeanCorner 22 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 22 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint22_14

namespace EndpointAnalyticJoint22_15
private noncomputable def weights : IntegerLookupTree := (.branch 1416 (.branch 993 (.branch 864 (.leaf (66388759500000:ℤ)) (.branch 939 (.leaf (7593815300000:ℤ)) (.leaf (4723844300000:ℤ)))) (.branch 1080 (.leaf (6870522100000:ℤ)) (.branch 1252 (.leaf (11322783200000:ℤ)) (.leaf (7439890600000:ℤ))))) (.branch 2008 (.branch 1515 (.leaf (3184041800000:ℤ)) (.branch 1727 (.leaf (5251406900000:ℤ)) (.leaf (4143418200000:ℤ)))) (.branch 2467 (.leaf (3206139600000:ℤ)) (.branch 3198 (.leaf (1478459800000:ℤ)) (.leaf (798803900000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 143 (.branch 127 (.leaf (1868657935540033:ℤ)) (.branch 135 (.leaf (2095318369811073:ℤ)) (.leaf (2216337482110219:ℤ)))) (.branch 150 (.leaf (2348097636633955:ℤ)) (.branch 157 (.leaf (2473268912461035:ℤ)) (.leaf (2608769500882152:ℤ))))) (.branch 187 (.branch 169 (.leaf (2691299619040328:ℤ)) (.branch 180 (.leaf (2868713089935870:ℤ)) (.leaf (3143350760658566:ℤ)))) (.branch 192 (.leaf (3339695736329498:ℤ)) (.branch 200 (.leaf (3491765179603695:ℤ)) (.leaf (3758387742075624:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1878052228544233:ℤ)) (.branch 135 (.leaf (2109995628209030:ℤ)) (.leaf (2234266800339123:ℤ)))) (.branch 150 (.leaf (2369895472145545:ℤ)) (.branch 157 (.leaf (2499048610048288:ℤ)) (.leaf (2639186075448030:ℤ))))) (.branch 187 (.branch 169 (.leaf (2724702243793077:ℤ)) (.branch 180 (.leaf (2908937120347367:ℤ)) (.leaf (3195175371426628:ℤ)))) (.branch 192 (.leaf (3400553977789953:ℤ)) (.branch 200 (.leaf (3560026124462386:ℤ)) (.leaf (3840449479384339:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1873930418876848:ℤ)) (.branch 135 (.leaf (2104233543620862:ℤ)) (.leaf (2227655604090292:ℤ)))) (.branch 150 (.leaf (2362411603100620:ℤ)) (.branch 157 (.leaf (2490807133389288:ℤ)) (.leaf (2630225667379607:ℤ))))) (.branch 187 (.branch 169 (.leaf (2715365023534958:ℤ)) (.branch 180 (.leaf (2898972715738507:ℤ)) (.leaf (3184820734083965:ℤ)))) (.branch 192 (.leaf (3390426452359448:ℤ)) (.branch 200 (.leaf (3550401663755495:ℤ)) (.leaf (3832467201789173:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1883705015317988:ℤ)) (.branch 135 (.leaf (2119573115449084:ℤ)) (.leaf (2246439195372272:ℤ)))) (.branch 150 (.leaf (2385308566301748:ℤ)) (.branch 157 (.leaf (2517955497626909:ℤ)) (.leaf (2662345827254185:ℤ))))) (.branch 187 (.branch 169 (.leaf (2750698329415899:ℤ)) (.branch 180 (.leaf (2941678100020057:ℤ)) (.leaf (3240159001731477:ℤ)))) (.branch 192 (.leaf (3455680589597564:ℤ)) (.branch 200 (.leaf (3623829928752166:ℤ)) (.leaf (3921245601182783:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 22 15) 8000 (endpointMeanRuns 22 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 22 15, EndpointRunConditions (endpointMeanCutoff 22 15) (endpointMeanBox 22 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 22 15 h) (endpointMeanCornerA 22 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 15, endpointJoint24Q (endpointMeanCornerK 22 15 h) (endpointMeanCornerA 22 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 22 15, endpointRunWeightQ (endpointMeanCutoff 22 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 22 15) = (108139861/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 22 15 h = (logRoundedQ ((endpointMeanCutoff 22 15:ℚ)/200)).2+(108139861/250000000000000:ℚ)+((endpointMeanRuns 22 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 22 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 22 15) r*endpointJoint24Q (endpointMeanCornerK 22 15 h) (endpointMeanCornerA 22 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 22 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 22 15 h≤endpointMeanCorner 22 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 22 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint22_15

namespace EndpointAnalyticJoint22_16
private noncomputable def weights : IntegerLookupTree := (.branch 1329 (.branch 993 (.branch 864 (.leaf (63311305900000:ℤ)) (.branch 939 (.leaf (7528787700000:ℤ)) (.leaf (4685192500000:ℤ)))) (.branch 1152 (.branch 1080 (.leaf (6816636300000:ℤ)) (.leaf (4731199800000:ℤ))) (.branch 1252 (.leaf (5648612900000:ℤ)) (.leaf (3530907200000:ℤ))))) (.branch 1727 (.branch 1416 (.leaf (3373076700000:ℤ)) (.branch 1515 (.leaf (3163394800000:ℤ)) (.leaf (5218878500000:ℤ)))) (.branch 2467 (.branch 2008 (.leaf (4119331800000:ℤ)) (.leaf (3188795400000:ℤ))) (.branch 3198 (.leaf (1471115800000:ℤ)) (.leaf (795211800000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 143 (.branch 127 (.leaf (1878052228544233:ℤ)) (.branch 135 (.leaf (2109995628209030:ℤ)) (.leaf (2234266800339123:ℤ)))) (.branch 157 (.branch 150 (.leaf (2369895472145545:ℤ)) (.leaf (2499048610048288:ℤ))) (.branch 161 (.leaf (2639186075448030:ℤ)) (.leaf (2724702243793077:ℤ))))) (.branch 180 (.branch 169 (.leaf (2814517442818942:ℤ)) (.branch 175 (.leaf (2908937120347367:ℤ)) (.leaf (3059939190982248:ℤ)))) (.branch 192 (.branch 187 (.leaf (3195175371426628:ℤ)) (.leaf (3400553977789953:ℤ))) (.branch 200 (.leaf (3560026124462386:ℤ)) (.leaf (3840449479384339:ℤ)))))), (.branch 165 (.branch 143 (.branch 127 (.leaf (1887493749422178:ℤ)) (.branch 135 (.leaf (2124775697672448:ℤ)) (.leaf (2252341159860138:ℤ)))) (.branch 157 (.branch 150 (.leaf (2391895661096613:ℤ)) (.leaf (2525097017925933:ℤ))) (.branch 161 (.leaf (2669957287711111:ℤ)) (.leaf (2758519439756136:ℤ))))) (.branch 180 (.branch 169 (.leaf (2851664189061171:ℤ)) (.branch 175 (.leaf (2949725157186769:ℤ)) (.leaf (3106843421551125:ℤ)))) (.branch 192 (.branch 187 (.leaf (3247854417631828:ℤ)) (.leaf (3462521220143317:ℤ))) (.branch 200 (.leaf (3629621510886687:ℤ)) (.leaf (3924302976668941:ℤ)))))), (.branch 165 (.branch 143 (.branch 127 (.leaf (1883705015317988:ℤ)) (.branch 135 (.leaf (2119573115449084:ℤ)) (.leaf (2246439195372272:ℤ)))) (.branch 157 (.branch 150 (.leaf (2385308566301748:ℤ)) (.leaf (2517955497626909:ℤ))) (.branch 161 (.leaf (2662345827254185:ℤ)) (.leaf (2750698329415899:ℤ))))) (.branch 180 (.branch 169 (.leaf (2843692516297489:ℤ)) (.branch 175 (.leaf (2941678100020057:ℤ)) (.leaf (3098867419306326:ℤ)))) (.branch 192 (.branch 187 (.leaf (3240159001731477:ℤ)) (.leaf (3455680589597564:ℤ))) (.branch 200 (.leaf (3623829928752166:ℤ)) (.leaf (3921245601182783:ℤ)))))), (.branch 165 (.branch 143 (.branch 127 (.leaf (1893530596968942:ℤ)) (.branch 135 (.leaf (2135024510636739:ℤ)) (.leaf (2265381169889439:ℤ)))) (.branch 157 (.branch 150 (.leaf (2408427451425014:ℤ)) (.leaf (2545399763410216:ℤ))) (.branch 161 (.leaf (2694858236616384:ℤ)) (.leaf (2786491404975565:ℤ))))) (.branch 180 (.branch 169 (.leaf (2883081972491806:ℤ)) (.branch 175 (.leaf (2985012586409648:ℤ)) (.leaf (3148855298943294:ℤ)))) (.branch 192 (.branch 187 (.leaf (3296458806659079:ℤ)) (.leaf (3522190646256591:ℤ))) (.branch 200 (.leaf (3698776813502615:ℤ)) (.leaf (4012080535905692:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 22 16) 8000 (endpointMeanRuns 22 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 22 16, EndpointRunConditions (endpointMeanCutoff 22 16) (endpointMeanBox 22 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 22 16 h) (endpointMeanCornerA 22 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 16, endpointJoint24Q (endpointMeanCornerK 22 16 h) (endpointMeanCornerA 22 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 22 16, endpointRunWeightQ (endpointMeanCutoff 22 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 22 16) = (431063013/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 22 16 h = (logRoundedQ ((endpointMeanCutoff 22 16:ℚ)/200)).2+(431063013/1000000000000000:ℚ)+((endpointMeanRuns 22 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 22 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 22 16) r*endpointJoint24Q (endpointMeanCornerK 22 16 h) (endpointMeanCornerA 22 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 22 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 22 16 h≤endpointMeanCorner 22 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 22 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint22_16

namespace EndpointAnalyticJoint22_17
private noncomputable def weights : IntegerLookupTree := (.branch 1329 (.branch 993 (.branch 864 (.leaf (60769626400000:ℤ)) (.branch 939 (.leaf (7473714700000:ℤ)) (.leaf (4652457700000:ℤ)))) (.branch 1152 (.branch 1080 (.leaf (6770999600000:ℤ)) (.leaf (4700908800000:ℤ))) (.branch 1252 (.leaf (5613919500000:ℤ)) (.leaf (3510064700000:ℤ))))) (.branch 2008 (.branch 1515 (.branch 1416 (.leaf (3353799900000:ℤ)) (.leaf (3145908500000:ℤ))) (.branch 1727 (.leaf (5191329700000:ℤ)) (.leaf (4098932600000:ℤ)))) (.branch 3198 (.branch 2467 (.leaf (3174106300000:ℤ)) (.leaf (1464896000000:ℤ))) (.branch 4544 (.leaf (348560500000:ℤ)) (.leaf (21782000000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 135 (.branch 119 (.leaf (1887493749422178:ℤ)) (.branch 127 (.leaf (2007827790626934:ℤ)) (.leaf (2124775697672448:ℤ)))) (.branch 150 (.branch 143 (.leaf (2252341159860138:ℤ)) (.leaf (2391895661096613:ℤ))) (.branch 157 (.leaf (2525097017925933:ℤ)) (.leaf (2669957287711111:ℤ))))) (.branch 180 (.branch 169 (.branch 165 (.leaf (2758519439756136:ℤ)) (.leaf (2851664189061171:ℤ))) (.branch 175 (.leaf (2949725157186769:ℤ)) (.leaf (3106843421551125:ℤ)))) (.branch 192 (.branch 187 (.leaf (3247854417631828:ℤ)) (.leaf (3462521220143317:ℤ))) (.branch 200 (.leaf (3629621510886687:ℤ)) (.leaf (3924302976668941:ℤ)))))), (.branch 161 (.branch 135 (.branch 119 (.leaf (1896982735602274:ℤ)) (.branch 127 (.leaf (2019917319906338:ℤ)) (.leaf (2139659298370921:ℤ)))) (.branch 150 (.branch 143 (.leaf (2270561734001559:ℤ)) (.leaf (2414100081972487:ℤ))) (.branch 157 (.leaf (2551416936949958:ℤ)) (.leaf (2701087272518863:ℤ))))) (.branch 180 (.branch 169 (.branch 165 (.leaf (2792756352312234:ℤ)) (.leaf (2889301207893437:ℤ))) (.branch 175 (.leaf (2991085108742915:ℤ)) (.leaf (3154466622892930:ℤ)))) (.branch 192 (.branch 187 (.leaf (3301401986401986:ℤ)) (.leaf (3525617672369535:ℤ))) (.branch 200 (.leaf (3700577426038085:ℤ)) (.leaf (4009987355740847:ℤ)))))), (.branch 161 (.branch 135 (.branch 119 (.leaf (1893530596968942:ℤ)) (.branch 127 (.leaf (2015844638655168:ℤ)) (.leaf (2135024510636739:ℤ)))) (.branch 150 (.branch 143 (.leaf (2265381169889439:ℤ)) (.leaf (2408427451425014:ℤ))) (.branch 157 (.leaf (2545399763410216:ℤ)) (.leaf (2694858236616384:ℤ))))) (.branch 180 (.branch 169 (.branch 165 (.leaf (2786491404975565:ℤ)) (.leaf (2883081972491806:ℤ))) (.branch 175 (.leaf (2985012586409648:ℤ)) (.leaf (3148855298943294:ℤ)))) (.branch 192 (.branch 187 (.leaf (3296458806659079:ℤ)) (.leaf (3522190646256591:ℤ))) (.branch 200 (.leaf (3698776813502615:ℤ)) (.leaf (4012080535905692:ℤ)))))), (.branch 161 (.branch 135 (.branch 119 (.leaf (1903407429773341:ℤ)) (.branch 127 (.leaf (2028457859323037:ℤ)) (.leaf (2150588544360664:ℤ)))) (.branch 150 (.branch 143 (.leaf (2284482863129168:ℤ)) (.leaf (2431770409381827:ℤ))) (.branch 157 (.leaf (2573143155895761:ℤ)) (.leaf (2727767685593695:ℤ))))) (.branch 180 (.branch 169 (.branch 165 (.leaf (2822750232902300:ℤ)) (.leaf (2923017032421541:ℤ))) (.branch 175 (.leaf (3028985442344378:ℤ)) (.leaf (3199649533861890:ℤ)))) (.branch 192 (.branch 187 (.leaf (3353736856183070:ℤ)) (.leaf (3589980794498766:ℤ))) (.branch 200 (.leaf (3775273725612031:ℤ)) (.leaf (4105019645221395:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 22 17) 8000 (endpointMeanRuns 22 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 22 17, EndpointRunConditions (endpointMeanCutoff 22 17) (endpointMeanBox 22 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 22 17 h) (endpointMeanCornerA 22 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 17, endpointJoint24Q (endpointMeanCornerK 22 17 h) (endpointMeanCornerA 22 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 22 17, endpointRunWeightQ (endpointMeanCutoff 22 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 22 17) = (214897831/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 22 17 h = (logRoundedQ ((endpointMeanCutoff 22 17:ℚ)/200)).2+(214897831/500000000000000:ℚ)+((endpointMeanRuns 22 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 22 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 22 17) r*endpointJoint24Q (endpointMeanCornerK 22 17 h) (endpointMeanCornerA 22 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 22 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 22 17 h≤endpointMeanCorner 22 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 22 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint22_17

namespace EndpointAnalyticJoint22_18
private noncomputable def weights : IntegerLookupTree := (.branch 1329 (.branch 993 (.branch 864 (.leaf (57912223400000:ℤ)) (.branch 939 (.leaf (7410220000000:ℤ)) (.leaf (4614717000000:ℤ)))) (.branch 1152 (.branch 1080 (.leaf (6718384100000:ℤ)) (.leaf (4665985800000:ℤ))) (.branch 1252 (.leaf (5573920800000:ℤ)) (.leaf (3486034900000:ℤ))))) (.branch 1727 (.branch 1416 (.leaf (3331575300000:ℤ)) (.branch 1515 (.leaf (3125748200000:ℤ)) (.leaf (5159568100000:ℤ)))) (.branch 2467 (.branch 2008 (.leaf (4075414000000:ℤ)) (.leaf (3157171000000:ℤ))) (.branch 3198 (.leaf (1457725100000:ℤ)) (.leaf (788662100000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 143 (.branch 127 (.leaf (1896982735602274:ℤ)) (.branch 135 (.leaf (2139659298370921:ℤ)) (.leaf (2270561734001559:ℤ)))) (.branch 157 (.branch 150 (.leaf (2414100081972487:ℤ)) (.leaf (2551416936949958:ℤ))) (.branch 161 (.leaf (2701087272518863:ℤ)) (.leaf (2792756352312234:ℤ))))) (.branch 180 (.branch 169 (.leaf (2889301207893437:ℤ)) (.branch 175 (.leaf (2991085108742915:ℤ)) (.leaf (3154466622892930:ℤ)))) (.branch 192 (.branch 187 (.leaf (3301401986401986:ℤ)) (.leaf (3525617672369535:ℤ))) (.branch 200 (.leaf (3700577426038085:ℤ)) (.leaf (4009987355740847:ℤ)))))), (.branch 165 (.branch 143 (.branch 127 (.leaf (1906519425706561:ℤ)) (.branch 135 (.leaf (2154647155518669:ℤ)) (.leaf (2288929705583453:ℤ)))) (.branch 157 (.branch 150 (.leaf (2436510630696854:ℤ)) (.leaf (2578011197170583:ℤ))) (.branch 161 (.leaf (2732580212928404:ℤ)) (.leaf (2827418190705170:ℤ))))) (.branch 180 (.branch 169 (.leaf (2927434970063162:ℤ)) (.branch 175 (.leaf (3033024994191738:ℤ)) (.leaf (3202819815740044:ℤ)))) (.branch 192 (.branch 187 (.leaf (3355832397120241:ℤ)) (.leaf (3589863911710522:ℤ))) (.branch 200 (.leaf (3772920467059181:ℤ)) (.leaf (4097542592608542:ℤ)))))), (.branch 165 (.branch 143 (.branch 127 (.leaf (1903407429773341:ℤ)) (.branch 135 (.leaf (2150588544360664:ℤ)) (.leaf (2284482863129168:ℤ)))) (.branch 157 (.branch 150 (.leaf (2431770409381827:ℤ)) (.leaf (2573143155895761:ℤ))) (.branch 161 (.leaf (2727767685593695:ℤ)) (.leaf (2822750232902300:ℤ))))) (.branch 180 (.branch 169 (.leaf (2923017032421541:ℤ)) (.branch 175 (.leaf (3028985442344378:ℤ)) (.leaf (3199649533861890:ℤ)))) (.branch 192 (.branch 187 (.leaf (3353736856183070:ℤ)) (.leaf (3589980794498766:ℤ))) (.branch 200 (.leaf (3775273725612031:ℤ)) (.leaf (4105019645221395:ℤ)))))), (.branch 165 (.branch 143 (.branch 127 (.leaf (1913335781061991:ℤ)) (.branch 135 (.leaf (2166266037740230:ℤ)) (.leaf (2303745621839682:ℤ)))) (.branch 157 (.branch 150 (.leaf (2455339611930669:ℤ)) (.leaf (2601188935392443:ℤ))) (.branch 161 (.leaf (2761079022810346:ℤ)) (.leaf (2859480873733342:ℤ))))) (.branch 180 (.branch 169 (.leaf (2963505253526303:ℤ)) (.branch 175 (.leaf (3073606071781927:ℤ)) (.leaf (3251263131391975:ℤ)))) (.branch 192 (.branch 187 (.leaf (3412010147919904:ℤ)) (.leaf (3659075671717945:ℤ))) (.branch 200 (.leaf (3853352722247576:ℤ)) (.leaf (4200111671948182:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 22 18) 8000 (endpointMeanRuns 22 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 22 18, EndpointRunConditions (endpointMeanCutoff 22 18) (endpointMeanBox 22 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 22 18 h) (endpointMeanCornerA 22 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 18, endpointJoint24Q (endpointMeanCornerK 22 18 h) (endpointMeanCornerA 22 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 22 18, endpointRunWeightQ (endpointMeanCutoff 22 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 22 18) = (428334507/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 22 18 h = (logRoundedQ ((endpointMeanCutoff 22 18:ℚ)/200)).2+(428334507/1000000000000000:ℚ)+((endpointMeanRuns 22 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 22 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 22 18) r*endpointJoint24Q (endpointMeanCornerK 22 18 h) (endpointMeanCornerA 22 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 22 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 22 18 h≤endpointMeanCorner 22 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 22 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint22_18

namespace EndpointAnalyticJoint22_19
private noncomputable def weights : IntegerLookupTree := (.branch 1252 (.branch 993 (.branch 864 (.leaf (55552159500000:ℤ)) (.branch 939 (.leaf (7356430100000:ℤ)) (.leaf (4582744800000:ℤ)))) (.branch 1080 (.leaf (6673810500000:ℤ)) (.branch 1152 (.leaf (4636400500000:ℤ)) (.leaf (5540035800000:ℤ))))) (.branch 1727 (.branch 1416 (.leaf (7254617000000:ℤ)) (.branch 1515 (.leaf (3108669300000:ℤ)) (.leaf (5132661100000:ℤ)))) (.branch 2467 (.branch 2008 (.leaf (4055490100000:ℤ)) (.leaf (3142824100000:ℤ))) (.branch 3198 (.leaf (1451650300000:ℤ)) (.leaf (785690800000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 143 (.branch 127 (.leaf (1906519425706561:ℤ)) (.branch 135 (.leaf (2154647155518669:ℤ)) (.leaf (2288929705583453:ℤ)))) (.branch 150 (.leaf (2436510630696854:ℤ)) (.branch 157 (.leaf (2578011197170583:ℤ)) (.leaf (2732580212928404:ℤ))))) (.branch 180 (.branch 169 (.leaf (2827418190705170:ℤ)) (.branch 175 (.leaf (3033024994191738:ℤ)) (.leaf (3202819815740044:ℤ)))) (.branch 192 (.branch 187 (.leaf (3355832397120241:ℤ)) (.leaf (3589863911710522:ℤ))) (.branch 200 (.leaf (3772920467059181:ℤ)) (.leaf (4097542592608542:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1916104059556687:ℤ)) (.branch 135 (.leaf (2169739999409889:ℤ)) (.leaf (2307446266994456:ℤ)))) (.branch 150 (.leaf (2459129220793607:ℤ)) (.branch 157 (.leaf (2604882658136575:ℤ)) (.leaf (2764440340768628:ℤ))))) (.branch 180 (.branch 169 (.leaf (2862510228832425:ℤ)) (.branch 175 (.leaf (3075552945151070:ℤ)) (.leaf (3251914189755960:ℤ)))) (.branch 192 (.branch 187 (.leaf (3411160205254252:ℤ)) (.leaf (3655280890380904:ℤ))) (.branch 200 (.leaf (3846677751043378:ℤ)) (.leaf (4187009536128372:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1913335781061991:ℤ)) (.branch 135 (.leaf (2166266037740230:ℤ)) (.leaf (2303745621839682:ℤ)))) (.branch 150 (.leaf (2455339611930669:ℤ)) (.branch 157 (.leaf (2601188935392443:ℤ)) (.leaf (2761079022810346:ℤ))))) (.branch 180 (.branch 169 (.leaf (2859480873733342:ℤ)) (.branch 175 (.leaf (3073606071781927:ℤ)) (.leaf (3251263131391975:ℤ)))) (.branch 192 (.branch 187 (.leaf (3412010147919904:ℤ)) (.leaf (3659075671717945:ℤ))) (.branch 200 (.leaf (3853352722247576:ℤ)) (.leaf (4200111671948182:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1923315919560130:ℤ)) (.branch 135 (.leaf (2182057817880653:ℤ)) (.leaf (2323170804124968:ℤ)))) (.branch 150 (.leaf (2479137251879131:ℤ)) (.branch 157 (.leaf (2629540397744650:ℤ)) (.leaf (2794797156101688:ℤ))))) (.branch 180 (.branch 169 (.leaf (2896689466867831:ℤ)) (.branch 175 (.leaf (3118884017211679:ℤ)) (.leaf (3303709308684883:ℤ)))) (.branch 192 (.branch 187 (.leaf (3471295974830324:ℤ)) (.leaf (3729500389493718:ℤ))) (.branch 200 (.leaf (3933046523572455:ℤ)) (.leaf (4297406488022761:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 22 19) 8000 (endpointMeanRuns 22 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 22 19, EndpointRunConditions (endpointMeanCutoff 22 19) (endpointMeanBox 22 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 22 19 h) (endpointMeanCornerA 22 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 19, endpointJoint24Q (endpointMeanCornerK 22 19 h) (endpointMeanCornerA 22 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 22 19, endpointRunWeightQ (endpointMeanCutoff 22 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 22 19) = (213548341/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 22 19 h = (logRoundedQ ((endpointMeanCutoff 22 19:ℚ)/200)).2+(213548341/500000000000000:ℚ)+((endpointMeanRuns 22 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 22 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 22 19) r*endpointJoint24Q (endpointMeanCornerK 22 19 h) (endpointMeanCornerA 22 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 22 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 22 19 h≤endpointMeanCorner 22 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 22 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint22_19

namespace EndpointAnalyticJoint22_20
private noncomputable def weights : IntegerLookupTree := (.branch 1252 (.branch 939 (.branch 864 (.leaf (52898809700000:ℤ)) (.leaf (7294397600000:ℤ))) (.branch 1041 (.leaf (8646742700000:ℤ)) (.branch 1122 (.leaf (5602010400000:ℤ)) (.leaf (7592962500000:ℤ))))) (.branch 2008 (.branch 1416 (.leaf (7206202100000:ℤ)) (.branch 1727 (.leaf (9090940600000:ℤ)) (.leaf (4032513100000:ℤ)))) (.branch 2467 (.leaf (3126278800000:ℤ)) (.branch 3198 (.leaf (1444644500000:ℤ)) (.leaf (782264100000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 135 (.branch 127 (.leaf (1916104059556687:ℤ)) (.leaf (2169739999409889:ℤ))) (.branch 143 (.leaf (2307446266994456:ℤ)) (.branch 150 (.leaf (2459129220793607:ℤ)) (.leaf (2604882658136575:ℤ))))) (.branch 183 (.branch 169 (.leaf (2862510228832425:ℤ)) (.branch 177 (.leaf (3075552945151070:ℤ)) (.leaf (3314201093430928:ℤ)))) (.branch 192 (.leaf (3512590028374580:ℤ)) (.branch 200 (.leaf (3846677751043378:ℤ)) (.leaf (4187009536128372:ℤ)))))), (.branch 161 (.branch 135 (.branch 127 (.leaf (1925736878179969:ℤ)) (.leaf (2184938565454341:ℤ))) (.branch 143 (.leaf (2326112620269163:ℤ)) (.branch 150 (.leaf (2481957783550244:ℤ)) (.leaf (2632034209202740:ℤ))))) (.branch 183 (.branch 169 (.leaf (2898037806047592:ℤ)) (.branch 177 (.leaf (3118677207257287:ℤ)) (.leaf (3366512785958173:ℤ)))) (.branch 192 (.leaf (3573056344522490:ℤ)) (.branch 200 (.leaf (3921876925199449:ℤ)) (.leaf (4278429927062568:ℤ)))))), (.branch 161 (.branch 135 (.branch 127 (.leaf (1923315919560130:ℤ)) (.leaf (2182057817880653:ℤ))) (.branch 143 (.leaf (2323170804124968:ℤ)) (.branch 150 (.leaf (2479137251879131:ℤ)) (.leaf (2629540397744650:ℤ))))) (.branch 183 (.branch 169 (.leaf (2896689466867831:ℤ)) (.branch 177 (.leaf (3118884017211679:ℤ)) (.leaf (3369179354919399:ℤ)))) (.branch 192 (.leaf (3578386013293245:ℤ)) (.branch 200 (.leaf (3933046523572455:ℤ)) (.leaf (4297406488022761:ℤ)))))), (.branch 161 (.branch 135 (.branch 127 (.leaf (1933348115394694:ℤ)) (.leaf (2197964717916625:ℤ))) (.branch 143 (.leaf (2342759779540552:ℤ)) (.branch 150 (.leaf (2503165543287927:ℤ)) (.leaf (2658200874719587:ℤ))))) (.branch 183 (.branch 169 (.leaf (2934382231592958:ℤ)) (.branch 177 (.leaf (3164828961695459:ℤ)) (.leaf (3425175323823078:ℤ)))) (.branch 192 (.leaf (3643364098441533:ℤ)) (.branch 200 (.leaf (4014388526457739:ℤ)) (.leaf (4396955120656136:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 22 20) 8000 (endpointMeanRuns 22 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 22 20, EndpointRunConditions (endpointMeanCutoff 22 20) (endpointMeanBox 22 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 22 20 h) (endpointMeanCornerA 22 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 20, endpointJoint24Q (endpointMeanCornerK 22 20 h) (endpointMeanCornerA 22 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 22 20, endpointRunWeightQ (endpointMeanCutoff 22 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 22 20) = (425669177/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 22 20 h = (logRoundedQ ((endpointMeanCutoff 22 20:ℚ)/200)).2+(425669177/1000000000000000:ℚ)+((endpointMeanRuns 22 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 22 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 22 20) r*endpointJoint24Q (endpointMeanCornerK 22 20 h) (endpointMeanCornerA 22 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 22 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 22 20 h≤endpointMeanCorner 22 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 22 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint22_20

namespace EndpointAnalyticJoint22_21
private noncomputable def weights : IntegerLookupTree := (.branch 1416 (.branch 1041 (.branch 864 (.leaf (50349149200000:ℤ)) (.leaf (17431896200000:ℤ))) (.branch 1252 (.leaf (14437611100000:ℤ)) (.leaf (7158380200000:ℤ)))) (.branch 2008 (.branch 1727 (.leaf (9035166400000:ℤ)) (.leaf (4009817500000:ℤ))) (.branch 2467 (.leaf (3109936100000:ℤ)) (.branch 3198 (.leaf (1437724600000:ℤ)) (.leaf (778879500000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 150 (.branch 135 (.branch 127 (.leaf (1925736878179969:ℤ)) (.leaf (2184938565454341:ℤ))) (.branch 143 (.leaf (2326112620269163:ℤ)) (.leaf (2481957783550244:ℤ)))) (.branch 169 (.branch 161 (.leaf (2632034209202740:ℤ)) (.leaf (2898037806047592:ℤ))) (.branch 183 (.leaf (3118677207257287:ℤ)) (.branch 200 (.leaf (3573056344522490:ℤ)) (.leaf (4278429927062568:ℤ)))))), (.branch 150 (.branch 135 (.branch 127 (.leaf (1935418123815433:ℤ)) (.leaf (2200243594213159:ℤ))) (.branch 143 (.leaf (2344929977166170:ℤ)) (.leaf (2504998268182773:ℤ)))) (.branch 169 (.branch 161 (.leaf (2659468769840563:ℤ)) (.leaf (2934006327972774:ℤ))) (.branch 183 (.leaf (3162406141763993:ℤ)) (.branch 200 (.leaf (3634563538017026:ℤ)) (.leaf (4371846417553366:ℤ)))))), (.branch 150 (.branch 135 (.branch 127 (.leaf (1933348115394694:ℤ)) (.leaf (2197964717916625:ℤ))) (.branch 143 (.leaf (2342759779540552:ℤ)) (.leaf (2503165543287927:ℤ)))) (.branch 169 (.branch 161 (.leaf (2658200874719587:ℤ)) (.leaf (2934382231592958:ℤ))) (.branch 183 (.leaf (3164828961695459:ℤ)) (.branch 200 (.leaf (3643364098441533:ℤ)) (.leaf (4396955120656136:ℤ)))))), (.branch 150 (.branch 135 (.branch 127 (.leaf (1943432640101616:ℤ)) (.leaf (2213987577056286:ℤ))) (.branch 143 (.leaf (2362513929190056:ℤ)) (.leaf (2527426721676899:ℤ)))) (.branch 169 (.branch 161 (.leaf (2687173734398790:ℤ)) (.leaf (2972565468123534:ℤ))) (.branch 183 (.leaf (3211450730938343:ℤ)) (.branch 200 (.leaf (3709522087472145:ℤ)) (.leaf (4498809779095254:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 22 21) 8000 (endpointMeanRuns 22 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 22 21, EndpointRunConditions (endpointMeanCutoff 22 21) (endpointMeanBox 22 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 22 21 h) (endpointMeanCornerA 22 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 22 21, endpointJoint24Q (endpointMeanCornerK 22 21 h) (endpointMeanCornerA 22 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 22 21, endpointRunWeightQ (endpointMeanCutoff 22 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 22 21) = (424259157/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 22 21 h = (logRoundedQ ((endpointMeanCutoff 22 21:ℚ)/200)).2+(424259157/1000000000000000:ℚ)+((endpointMeanRuns 22 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 22 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 22 21) r*endpointJoint24Q (endpointMeanCornerK 22 21 h) (endpointMeanCornerA 22 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 22 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 22 21 h≤endpointMeanCorner 22 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 22 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint22_21

namespace EndpointAnalyticJoint23_06
private noncomputable def weights : IntegerLookupTree := (.branch 1141 (.branch 844 (.leaf (90752714400000:ℤ)) (.leaf (35821573800000:ℤ))) (.branch 1962 (.leaf (45740725000000:ℤ)) (.leaf (21164731500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 174 (.branch 143 (.leaf (1790178752538225:ℤ)) (.leaf (2170403433375676:ℤ))) (.branch 200 (.leaf (2632487790882928:ℤ)) (.leaf (3133800939280413:ℤ)))), (.branch 174 (.branch 143 (.leaf (1797537653771089:ℤ)) (.leaf (2186973700118722:ℤ))) (.branch 200 (.leaf (2665418139707037:ℤ)) (.leaf (3190903464613988:ℤ)))), (.branch 174 (.branch 143 (.leaf (1792347794673344:ℤ)) (.leaf (2176174052928171:ℤ))) (.branch 200 (.leaf (2646151357118619:ℤ)) (.leaf (3161804098192690:ℤ)))), (.branch 174 (.branch 143 (.leaf (1799992281388754:ℤ)) (.leaf (2193527624206087:ℤ))) (.branch 200 (.leaf (2681013971038825:ℤ)) (.leaf (3223054690937450:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 23 6) 8000 (endpointMeanRuns 23 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 23 6, EndpointRunConditions (endpointMeanCutoff 23 6) (endpointMeanBox 23 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 23 6 h) (endpointMeanCornerA 23 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 6, endpointJoint24Q (endpointMeanCornerK 23 6 h) (endpointMeanCornerA 23 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 23 6, endpointRunWeightQ (endpointMeanCutoff 23 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 23 6) = (444092037/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 23 6 h = (logRoundedQ ((endpointMeanCutoff 23 6:ℚ)/200)).2+(444092037/1000000000000000:ℚ)+((endpointMeanRuns 23 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 23 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 23 6) r*endpointJoint24Q (endpointMeanCornerK 23 6 h) (endpointMeanCornerA 23 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 23 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 23 6 h≤endpointMeanCorner 23 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 23 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint23_06

namespace EndpointAnalyticJoint23_07
private noncomputable def weights : IntegerLookupTree := (.branch 1141 (.branch 844 (.leaf (87225724300000:ℤ)) (.leaf (35559136200000:ℤ))) (.branch 1962 (.leaf (45463618700000:ℤ)) (.leaf (21062819900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 174 (.branch 143 (.leaf (1797537653771089:ℤ)) (.leaf (2186973700118722:ℤ))) (.branch 200 (.leaf (2665418139707037:ℤ)) (.leaf (3190903464613988:ℤ)))), (.branch 174 (.branch 143 (.leaf (1806913778400033:ℤ)) (.leaf (2208170284265083:ℤ))) (.branch 200 (.leaf (2707773729265756:ℤ)) (.leaf (3264820157775953:ℤ)))), (.branch 174 (.branch 143 (.leaf (1799992281388754:ℤ)) (.leaf (2193527624206087:ℤ))) (.branch 200 (.leaf (2681013971038825:ℤ)) (.leaf (3223054690937450:ℤ)))), (.branch 174 (.branch 143 (.leaf (1809733974700244:ℤ)) (.leaf (2215734697206856:ℤ))) (.branch 200 (.leaf (2725888325871439:ℤ)) (.leaf (3302442570610780:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 23 7) 8000 (endpointMeanRuns 23 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 23 7, EndpointRunConditions (endpointMeanCutoff 23 7) (endpointMeanBox 23 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 23 7 h) (endpointMeanCornerA 23 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 7, endpointJoint24Q (endpointMeanCornerK 23 7 h) (endpointMeanCornerA 23 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 23 7, endpointRunWeightQ (endpointMeanCutoff 23 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 23 7) = (88534749/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 23 7 h = (logRoundedQ ((endpointMeanCutoff 23 7:ℚ)/200)).2+(88534749/200000000000000:ℚ)+((endpointMeanRuns 23 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 23 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 23 7) r*endpointJoint24Q (endpointMeanCornerK 23 7 h) (endpointMeanCornerA 23 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 23 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 23 7 h≤endpointMeanCorner 23 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 23 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint23_07

namespace EndpointAnalyticJoint23_08
private noncomputable def weights : IntegerLookupTree := (.branch 1141 (.branch 844 (.leaf (83262572800000:ℤ)) (.leaf (35256990600000:ℤ))) (.branch 1962 (.leaf (45144584800000:ℤ)) (.leaf (20945488600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 174 (.branch 143 (.leaf (1806913778400033:ℤ)) (.leaf (2208170284265083:ℤ))) (.branch 200 (.leaf (2707773729265756:ℤ)) (.leaf (3264820157775953:ℤ)))), (.branch 174 (.branch 143 (.leaf (1816338809772533:ℤ)) (.leaf (2229572309921524:ℤ))) (.branch 200 (.leaf (2750802382438827:ℤ)) (.leaf (3340449117569792:ℤ)))), (.branch 174 (.branch 143 (.leaf (1809733974700244:ℤ)) (.leaf (2215734697206856:ℤ))) (.branch 200 (.leaf (2725888325871439:ℤ)) (.leaf (3302442570610780:ℤ)))), (.branch 174 (.branch 143 (.leaf (1819528390787023:ℤ)) (.leaf (2238166592583160:ℤ))) (.branch 200 (.leaf (2771513780005806:ℤ)) (.leaf (3383785873335652:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 23 8) 8000 (endpointMeanRuns 23 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 23 8, EndpointRunConditions (endpointMeanCutoff 23 8) (endpointMeanBox 23 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 23 8 h) (endpointMeanCornerA 23 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 8, endpointJoint24Q (endpointMeanCornerK 23 8 h) (endpointMeanCornerA 23 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 23 8, endpointRunWeightQ (endpointMeanCutoff 23 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 23 8) = (220520429/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 23 8 h = (logRoundedQ ((endpointMeanCutoff 23 8:ℚ)/200)).2+(220520429/500000000000000:ℚ)+((endpointMeanRuns 23 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 23 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 23 8) r*endpointJoint24Q (endpointMeanCornerK 23 8 h) (endpointMeanCornerA 23 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 23 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 23 8 h≤endpointMeanCorner 23 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 23 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint23_08

namespace EndpointAnalyticJoint23_09
private noncomputable def weights : IntegerLookupTree := (.branch 1141 (.branch 844 (.leaf (79990746700000:ℤ)) (.leaf (35001376600000:ℤ))) (.branch 1384 (.leaf (14993679900000:ℤ)) (.branch 1962 (.leaf (18618521900000:ℤ)) (.leaf (20846226800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 143 (.leaf (1816338809772533:ℤ)) (.leaf (2229572309921524:ℤ))) (.branch 174 (.leaf (2512694880596515:ℤ)) (.branch 200 (.leaf (2750802382438827:ℤ)) (.leaf (3340449117569792:ℤ))))), (.branch 161 (.branch 143 (.leaf (1825813002990732:ℤ)) (.leaf (2251181768268045:ℤ))) (.branch 174 (.leaf (2545390969716060:ℤ)) (.branch 200 (.leaf (2794514794736184:ℤ)) (.leaf (3417830008337799:ℤ))))), (.branch 161 (.branch 143 (.leaf (1819528390787023:ℤ)) (.leaf (2238166592583160:ℤ))) (.branch 174 (.leaf (2527051559185415:ℤ)) (.branch 200 (.leaf (2771513780005806:ℤ)) (.leaf (3383785873335652:ℤ))))), (.branch 161 (.branch 143 (.leaf (1829375814988713:ℤ)) (.leaf (2260825586416156:ℤ))) (.branch 174 (.leaf (2561555526973998:ℤ)) (.branch 200 (.leaf (2817902905214009:ℤ)) (.leaf (3467132763634482:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 23 9) 8000 (endpointMeanRuns 23 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 23 9, EndpointRunConditions (endpointMeanCutoff 23 9) (endpointMeanBox 23 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 23 9 h) (endpointMeanCornerA 23 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 9, endpointJoint24Q (endpointMeanCornerK 23 9 h) (endpointMeanCornerA 23 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 23 9, endpointRunWeightQ (endpointMeanCutoff 23 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 23 9) = (219829721/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 23 9 h = (logRoundedQ ((endpointMeanCutoff 23 9:ℚ)/200)).2+(219829721/500000000000000:ℚ)+((endpointMeanRuns 23 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 23 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 23 9) r*endpointJoint24Q (endpointMeanCornerK 23 9 h) (endpointMeanCornerA 23 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 23 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 23 9 h≤endpointMeanCorner 23 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 23 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint23_09

namespace EndpointAnalyticJoint23_10
private noncomputable def weights : IntegerLookupTree := (.branch 1141 (.branch 844 (.leaf (76313940100000:ℤ)) (.leaf (34706986200000:ℤ))) (.branch 1962 (.leaf (44563838200000:ℤ)) (.branch 3125 (.leaf (7518928300000:ℤ)) (.leaf (985495100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 143 (.branch 127 (.leaf (1825813002990732:ℤ)) (.leaf (2029184914265818:ℤ))) (.branch 174 (.leaf (2251181768268045:ℤ)) (.branch 200 (.leaf (2794514794736184:ℤ)) (.leaf (3417830008337799:ℤ))))), (.branch 143 (.branch 127 (.leaf (1835336614487426:ℤ)) (.leaf (2043977391954185:ℤ))) (.branch 174 (.leaf (2273000669783530:ℤ)) (.branch 200 (.leaf (2838921831627825:ℤ)) (.leaf (3497003413239475:ℤ))))), (.branch 143 (.branch 127 (.leaf (1829375814988713:ℤ)) (.leaf (2035202610726513:ℤ))) (.branch 174 (.leaf (2260825586416156:ℤ)) (.branch 200 (.leaf (2817902905214009:ℤ)) (.leaf (3467132763634482:ℤ))))), (.branch 143 (.branch 127 (.leaf (1839276534189204:ℤ)) (.leaf (2050646100856768:ℤ))) (.branch 174 (.leaf (2283713977829842:ℤ)) (.branch 200 (.leaf (2865068483692296:ℤ)) (.leaf (3552532592382297:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 23 10) 8000 (endpointMeanRuns 23 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 23 10, EndpointRunConditions (endpointMeanCutoff 23 10) (endpointMeanBox 23 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 23 10 h) (endpointMeanCornerA 23 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 10, endpointJoint24Q (endpointMeanCornerK 23 10 h) (endpointMeanCornerA 23 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 23 10, endpointRunWeightQ (endpointMeanCutoff 23 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 23 10) = (219034233/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 23 10 h = (logRoundedQ ((endpointMeanCutoff 23 10:ℚ)/200)).2+(219034233/500000000000000:ℚ)+((endpointMeanRuns 23 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 23 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 23 10) r*endpointJoint24Q (endpointMeanCornerK 23 10 h) (endpointMeanCornerA 23 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 23 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 23 10 h≤endpointMeanCorner 23 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 23 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint23_10

namespace EndpointAnalyticJoint23_11
private noncomputable def weights : IntegerLookupTree := (.branch 1384 (.branch 844 (.leaf (72782381400000:ℤ)) (.branch 1141 (.leaf (34416609000000:ℤ)) (.leaf (14777313600000:ℤ)))) (.branch 1962 (.leaf (18379620200000:ℤ)) (.branch 3125 (.leaf (7477543400000:ℤ)) (.leaf (980890600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 127 (.leaf (1835336614487426:ℤ)) (.branch 143 (.leaf (2043977391954185:ℤ)) (.leaf (2273000669783530:ℤ)))) (.branch 174 (.leaf (2578512512101730:ℤ)) (.branch 200 (.leaf (2838921831627825:ℤ)) (.leaf (3497003413239475:ℤ))))), (.branch 161 (.branch 127 (.leaf (1844909902032973:ℤ)) (.branch 143 (.leaf (2058877704761288:ℤ)) (.leaf (2295031044432833:ℤ)))) (.branch 174 (.leaf (2612065043904367:ℤ)) (.branch 200 (.leaf (2884034531244601:ℤ)) (.leaf (3578010855535771:ℤ))))), (.branch 161 (.branch 127 (.leaf (1839276534189204:ℤ)) (.branch 143 (.leaf (2050646100856768:ℤ)) (.leaf (2283713977829842:ℤ)))) (.branch 174 (.leaf (2596530606556412:ℤ)) (.branch 200 (.leaf (2865068483692296:ℤ)) (.leaf (3552532592382297:ℤ))))), (.branch 161 (.branch 127 (.leaf (1849230836825027:ℤ)) (.branch 143 (.leaf (2066206779018406:ℤ)) (.leaf (2306834089224342:ℤ)))) (.branch 174 (.leaf (2631983230419602:ℤ)) (.branch 200 (.leaf (2913023511583154:ℤ)) (.leaf (3640035926028061:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 23 11) 8000 (endpointMeanRuns 23 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 23 11, EndpointRunConditions (endpointMeanCutoff 23 11) (endpointMeanBox 23 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 23 11 h) (endpointMeanCornerA 23 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 11, endpointJoint24Q (endpointMeanCornerK 23 11 h) (endpointMeanCornerA 23 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 23 11, endpointRunWeightQ (endpointMeanCutoff 23 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 23 11) = (21824959/50000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 23 11 h = (logRoundedQ ((endpointMeanCutoff 23 11:ℚ)/200)).2+(21824959/50000000000000:ℚ)+((endpointMeanRuns 23 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 23 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 23 11) r*endpointJoint24Q (endpointMeanCornerK 23 11 h) (endpointMeanCornerA 23 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 23 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 23 11 h≤endpointMeanCorner 23 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 23 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint23_11

namespace EndpointAnalyticJoint23_12
private noncomputable def weights : IntegerLookupTree := (.branch 1384 (.branch 844 (.leaf (69866458200000:ℤ)) (.branch 1141 (.leaf (34170826500000:ℤ)) (.leaf (14686373100000:ℤ)))) (.branch 1962 (.leaf (18279208000000:ℤ)) (.branch 3125 (.leaf (7442514100000:ℤ)) (.leaf (976993300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 127 (.leaf (1844909902032973:ℤ)) (.branch 143 (.leaf (2058877704761288:ℤ)) (.leaf (2295031044432833:ℤ)))) (.branch 174 (.leaf (2612065043904367:ℤ)) (.branch 200 (.leaf (2884034531244601:ℤ)) (.leaf (3578010855535771:ℤ))))), (.branch 161 (.branch 127 (.leaf (1854533124742303:ℤ)) (.branch 143 (.leaf (2073886638790241:ℤ)) (.leaf (2317274941855644:ℤ)))) (.branch 174 (.leaf (2646054173313216:ℤ)) (.branch 200 (.leaf (2929864107121954:ℤ)) (.leaf (3660894820366343:ℤ))))), (.branch 161 (.branch 127 (.leaf (1849230836825027:ℤ)) (.branch 143 (.leaf (2066206779018406:ℤ)) (.leaf (2306834089224342:ℤ)))) (.branch 174 (.leaf (2631983230419602:ℤ)) (.branch 200 (.leaf (2913023511583154:ℤ)) (.leaf (3640035926028061:ℤ))))), (.branch 161 (.branch 127 (.leaf (1859239012893762:ℤ)) (.branch 143 (.leaf (2081885534455660:ℤ)) (.leaf (2330188266511548:ℤ)))) (.branch 174 (.leaf (2667919918878690:ℤ)) (.branch 200 (.leaf (2961781202556272:ℤ)) (.leaf (3729694576535812:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 23 12) 8000 (endpointMeanRuns 23 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 23 12, EndpointRunConditions (endpointMeanCutoff 23 12) (endpointMeanBox 23 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 23 12 h) (endpointMeanCornerA 23 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 12, endpointJoint24Q (endpointMeanCornerK 23 12 h) (endpointMeanCornerA 23 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 23 12, endpointRunWeightQ (endpointMeanCutoff 23 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 23 12) = (27198181/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 23 12 h = (logRoundedQ ((endpointMeanCutoff 23 12:ℚ)/200)).2+(27198181/62500000000000:ℚ)+((endpointMeanRuns 23 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 23 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 23 12) r*endpointJoint24Q (endpointMeanCornerK 23 12 h) (endpointMeanCornerA 23 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 23 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 23 12 h≤endpointMeanCorner 23 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 23 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint23_12

namespace EndpointAnalyticJoint23_13
private noncomputable def weights : IntegerLookupTree := (.branch 1384 (.branch 959 (.branch 844 (.leaf (66589194200000:ℤ)) (.leaf (12875690100000:ℤ))) (.branch 1141 (.leaf (16267686600000:ℤ)) (.leaf (14581585300000:ℤ)))) (.branch 1962 (.branch 1623 (.leaf (8315338000000:ℤ)) (.leaf (6544947500000:ℤ))) (.branch 3125 (.leaf (7402151100000:ℤ)) (.leaf (972502500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 143 (.branch 127 (.leaf (1854533124742303:ℤ)) (.leaf (2073886638790241:ℤ))) (.branch 152 (.leaf (2317274941855644:ℤ)) (.leaf (2473427825702080:ℤ)))) (.branch 188 (.branch 174 (.leaf (2646054173313216:ℤ)) (.leaf (2929864107121954:ℤ))) (.branch 200 (.leaf (3291691977969955:ℤ)) (.leaf (3660894820366343:ℤ))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1864206543081888:ℤ)) (.leaf (2089004985874745:ℤ))) (.branch 152 (.leaf (2339734431557158:ℤ)) (.leaf (2501286888225771:ℤ)))) (.branch 188 (.branch 174 (.leaf (2680485581493292:ℤ)) (.leaf (2976421950987206:ℤ))) (.branch 200 (.leaf (3355968172499205:ℤ)) (.leaf (3745698777031313:ℤ))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1859239012893762:ℤ)) (.leaf (2081885534455660:ℤ))) (.branch 152 (.leaf (2330188266511548:ℤ)) (.leaf (2490247518051425:ℤ)))) (.branch 188 (.branch 174 (.leaf (2667919918878690:ℤ)) (.leaf (2961781202556272:ℤ))) (.branch 200 (.leaf (3339798360989644:ℤ)) (.leaf (3729694576535812:ℤ))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1869301353962468:ℤ)) (.leaf (2097683263160524:ℤ))) (.branch 152 (.leaf (2353778879353131:ℤ)) (.leaf (2519609202625881:ℤ)))) (.branch 188 (.branch 174 (.leaf (2704347281276146:ℤ)) (.leaf (3011354991449500:ℤ))) (.branch 200 (.leaf (3408816225198704:ℤ)) (.leaf (3821561632063245:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 23 13) 8000 (endpointMeanRuns 23 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 23 13, EndpointRunConditions (endpointMeanCutoff 23 13) (endpointMeanBox 23 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 23 13 h) (endpointMeanCornerA 23 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 13, endpointJoint24Q (endpointMeanCornerK 23 13 h) (endpointMeanCornerA 23 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 23 13, endpointRunWeightQ (endpointMeanCutoff 23 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 23 13) = (433640359/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 23 13 h = (logRoundedQ ((endpointMeanCutoff 23 13:ℚ)/200)).2+(433640359/1000000000000000:ℚ)+((endpointMeanRuns 23 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 23 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 23 13) r*endpointJoint24Q (endpointMeanCornerK 23 13 h) (endpointMeanCornerA 23 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 23 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 23 13 h≤endpointMeanCorner 23 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 23 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint23_13

namespace EndpointAnalyticJoint23_14
private noncomputable def weights : IntegerLookupTree := (.branch 1384 (.branch 959 (.branch 844 (.leaf (63441006600000:ℤ)) (.leaf (12764817300000:ℤ))) (.branch 1141 (.leaf (16139882800000:ℤ)) (.leaf (14478172400000:ℤ)))) (.branch 1962 (.branch 1623 (.leaf (8261565800000:ℤ)) (.leaf (6505871300000:ℤ))) (.branch 2411 (.leaf (3669324200000:ℤ)) (.branch 3125 (.leaf (1738164700000:ℤ)) (.leaf (968070700000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 152 (.branch 135 (.branch 127 (.leaf (1864206543081888:ℤ)) (.leaf (2089004985874745:ℤ))) (.branch 143 (.leaf (2209029071722778:ℤ)) (.leaf (2339734431557158:ℤ)))) (.branch 174 (.branch 161 (.leaf (2501286888225771:ℤ)) (.leaf (2680485581493292:ℤ))) (.branch 188 (.leaf (2976421950987206:ℤ)) (.branch 200 (.leaf (3355968172499205:ℤ)) (.leaf (3745698777031313:ℤ)))))), (.branch 152 (.branch 135 (.branch 127 (.leaf (1873930418876848:ℤ)) (.leaf (2104233543620862:ℤ))) (.branch 143 (.leaf (2227655604090292:ℤ)) (.leaf (2362411603100620:ℤ)))) (.branch 174 (.branch 161 (.leaf (2529459736887324:ℤ)) (.leaf (2715365023534958:ℤ))) (.branch 188 (.leaf (3023719635591180:ℤ)) (.branch 200 (.leaf (3421499475103816:ℤ)) (.leaf (3832467201789173:ℤ)))))), (.branch 152 (.branch 135 (.branch 127 (.leaf (1869301353962468:ℤ)) (.leaf (2097683263160524:ℤ))) (.branch 143 (.leaf (2220088617190393:ℤ)) (.leaf (2353778879353131:ℤ)))) (.branch 174 (.branch 161 (.leaf (2519609202625881:ℤ)) (.leaf (2704347281276146:ℤ))) (.branch 188 (.leaf (3011354991449500:ℤ)) (.branch 200 (.leaf (3408816225198704:ℤ)) (.leaf (3821561632063245:ℤ)))))), (.branch 152 (.branch 135 (.branch 127 (.leaf (1879418153176188:ℤ)) (.leaf (2113600867923945:ℤ))) (.branch 143 (.leaf (2239607165486249:ℤ)) (.leaf (2377608321401028:ℤ)))) (.branch 174 (.branch 161 (.leaf (2549317081108691:ℤ)) (.leaf (2741272017197393:ℤ))) (.branch 188 (.leaf (3061758537970709:ℤ)) (.branch 200 (.leaf (3479260362812655:ℤ)) (.leaf (3915691488395978:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 23 14) 8000 (endpointMeanRuns 23 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 23 14, EndpointRunConditions (endpointMeanCutoff 23 14) (endpointMeanBox 23 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 23 14 h) (endpointMeanCornerA 23 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 14, endpointJoint24Q (endpointMeanCornerK 23 14 h) (endpointMeanCornerA 23 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 23 14, endpointRunWeightQ (endpointMeanCutoff 23 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 23 14) = (432129903/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 23 14 h = (logRoundedQ ((endpointMeanCutoff 23 14:ℚ)/200)).2+(432129903/1000000000000000:ℚ)+((endpointMeanRuns 23 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 23 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 23 14) r*endpointJoint24Q (endpointMeanCornerK 23 14 h) (endpointMeanCornerA 23 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 23 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 23 14 h≤endpointMeanCorner 23 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 23 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint23_14

namespace EndpointAnalyticJoint23_15
private noncomputable def weights : IntegerLookupTree := (.branch 1279 (.branch 959 (.branch 844 (.leaf (60841356000000:ℤ)) (.leaf (12670927700000:ℤ))) (.branch 1055 (.leaf (8436675900000:ℤ)) (.branch 1141 (.leaf (6225445100000:ℤ)) (.leaf (8312012100000:ℤ))))) (.branch 1962 (.branch 1384 (.leaf (4729591200000:ℤ)) (.branch 1623 (.leaf (8216030300000:ℤ)) (.leaf (6472780800000:ℤ)))) (.branch 2411 (.leaf (3652169600000:ℤ)) (.branch 3125 (.leaf (1730711100000:ℤ)) (.leaf (964317700000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 135 (.branch 127 (.leaf (1873930418876848:ℤ)) (.leaf (2104233543620862:ℤ))) (.branch 143 (.leaf (2227655604090292:ℤ)) (.branch 152 (.leaf (2362411603100620:ℤ)) (.leaf (2529459736887324:ℤ))))) (.branch 180 (.branch 166 (.leaf (2715365023534958:ℤ)) (.branch 174 (.leaf (2827924551386247:ℤ)) (.leaf (3023719635591180:ℤ)))) (.branch 188 (.leaf (3184820734083965:ℤ)) (.branch 200 (.leaf (3421499475103816:ℤ)) (.leaf (3832467201789173:ℤ)))))), (.branch 161 (.branch 135 (.branch 127 (.leaf (1883705015317988:ℤ)) (.leaf (2119573115449084:ℤ))) (.branch 143 (.leaf (2246439195372272:ℤ)) (.branch 152 (.leaf (2385308566301748:ℤ)) (.leaf (2557949905967194:ℤ))))) (.branch 180 (.branch 166 (.leaf (2750698329415899:ℤ)) (.branch 174 (.leaf (2867706571867167:ℤ)) (.leaf (3071768917584818:ℤ)))) (.branch 188 (.leaf (3240159001731477:ℤ)) (.branch 200 (.leaf (3488310394021915:ℤ)) (.leaf (3921245601182783:ℤ)))))), (.branch 161 (.branch 135 (.branch 127 (.leaf (1879418153176188:ℤ)) (.leaf (2113600867923945:ℤ))) (.branch 143 (.leaf (2239607165486249:ℤ)) (.branch 152 (.leaf (2377608321401028:ℤ)) (.leaf (2549317081108691:ℤ))))) (.branch 180 (.branch 166 (.leaf (2741272017197393:ℤ)) (.branch 174 (.leaf (2857951022324844:ℤ)) (.leaf (3061758537970709:ℤ)))) (.branch 188 (.leaf (3230280589653117:ℤ)) (.branch 200 (.leaf (3479260362812655:ℤ)) (.leaf (3915691488395978:ℤ)))))), (.branch 161 (.branch 135 (.branch 127 (.leaf (1889589705266492:ℤ)) (.leaf (2129639258387408:ℤ))) (.branch 143 (.leaf (2259297316719316:ℤ)) (.branch 152 (.leaf (2401679010540265:ℤ)) (.leaf (2579375235357695:ℤ))))) (.branch 180 (.branch 166 (.leaf (2778700917702932:ℤ)) (.branch 174 (.leaf (2900196824297323:ℤ)) (.leaf (3113005730461630:ℤ)))) (.branch 188 (.leaf (3289515436566105:ℤ)) (.branch 200 (.leaf (3551160248169029:ℤ)) (.leaf (4012139881156033:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 23 15) 8000 (endpointMeanRuns 23 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 23 15, EndpointRunConditions (endpointMeanCutoff 23 15) (endpointMeanBox 23 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 23 15 h) (endpointMeanCornerA 23 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 15, endpointJoint24Q (endpointMeanCornerK 23 15 h) (endpointMeanCornerA 23 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 23 15, endpointRunWeightQ (endpointMeanCutoff 23 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 23 15) = (430850817/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 23 15 h = (logRoundedQ ((endpointMeanCutoff 23 15:ℚ)/200)).2+(430850817/1000000000000000:ℚ)+((endpointMeanRuns 23 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 23 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 23 15) r*endpointJoint24Q (endpointMeanCornerK 23 15 h) (endpointMeanCornerA 23 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 23 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 23 15 h≤endpointMeanCorner 23 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 23 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint23_15

namespace EndpointAnalyticJoint23_16
private noncomputable def weights : IntegerLookupTree := (.branch 1206 (.branch 959 (.branch 844 (.leaf (57919289700000:ℤ)) (.branch 889 (.leaf (4816892500000:ℤ)) (.leaf (6959506000000:ℤ)))) (.branch 1017 (.leaf (5037438100000:ℤ)) (.branch 1111 (.leaf (7292446100000:ℤ)) (.leaf (6081516300000:ℤ))))) (.branch 1962 (.branch 1384 (.leaf (9184712000000:ℤ)) (.branch 1623 (.leaf (8163537300000:ℤ)) (.leaf (6434634200000:ℤ)))) (.branch 2411 (.leaf (3632393800000:ℤ)) (.branch 3125 (.leaf (1722118700000:ℤ)) (.leaf (959991300000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 170 (.branch 143 (.branch 127 (.leaf (1883705015317988:ℤ)) (.branch 135 (.leaf (2119573115449084:ℤ)) (.leaf (2246439195372272:ℤ)))) (.branch 152 (.leaf (2385308566301748:ℤ)) (.branch 161 (.leaf (2557949905967194:ℤ)) (.leaf (2750698329415899:ℤ))))) (.branch 188 (.branch 176 (.leaf (2966998651143305:ℤ)) (.branch 183 (.leaf (3126342465209423:ℤ)) (.leaf (3329857437733672:ℤ)))) (.branch 195 (.leaf (3488310394021915:ℤ)) (.branch 200 (.leaf (3731028232233297:ℤ)) (.leaf (3921245601182783:ℤ)))))), (.branch 170 (.branch 143 (.branch 127 (.leaf (1893530596968942:ℤ)) (.branch 135 (.leaf (2135024510636739:ℤ)) (.leaf (2265381169889439:ℤ)))) (.branch 152 (.leaf (2408427451425014:ℤ)) (.branch 161 (.leaf (2586760969553651:ℤ)) (.leaf (2786491404975565:ℤ))))) (.branch 188 (.branch 176 (.leaf (3011378107804199:ℤ)) (.branch 183 (.leaf (3177533497270540:ℤ)) (.leaf (3390322619331444:ℤ)))) (.branch 195 (.leaf (3556425916058955:ℤ)) (.branch 200 (.leaf (3811562089918661:ℤ)) (.leaf (4012080535905692:ℤ)))))), (.branch 170 (.branch 143 (.branch 127 (.leaf (1889589705266492:ℤ)) (.branch 135 (.leaf (2129639258387408:ℤ)) (.leaf (2259297316719316:ℤ)))) (.branch 152 (.leaf (2401679010540265:ℤ)) (.branch 161 (.leaf (2579375235357695:ℤ)) (.leaf (2778700917702932:ℤ))))) (.branch 188 (.branch 176 (.leaf (3003597081017134:ℤ)) (.branch 183 (.leaf (3170120361145744:ℤ)) (.leaf (3383878980248656:ℤ)))) (.branch 195 (.leaf (3551160248169029:ℤ)) (.branch 200 (.leaf (3808883239952829:ℤ)) (.leaf (4012139881156033:ℤ)))))), (.branch 170 (.branch 143 (.branch 127 (.leaf (1899816306560057:ℤ)) (.branch 135 (.leaf (2145799351094920:ℤ)) (.leaf (2279160579586226:ℤ)))) (.branch 152 (.leaf (2425993389134338:ℤ)) (.branch 161 (.leaf (2609787795358550:ℤ)) (.leaf (2816640866577361:ℤ))))) (.branch 188 (.branch 176 (.leaf (3050860737290172:ℤ)) (.branch 183 (.leaf (3224829734122563:ℤ)) (.leaf (3448792246205305:ℤ)))) (.branch 195 (.leaf (3624545964700764:ℤ)) (.branch 200 (.leaf (3896123308794026:ℤ)) (.leaf (4110963918803730:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 23 16) 8000 (endpointMeanRuns 23 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 23 16, EndpointRunConditions (endpointMeanCutoff 23 16) (endpointMeanBox 23 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 23 16 h) (endpointMeanCornerA 23 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 16, endpointJoint24Q (endpointMeanCornerK 23 16 h) (endpointMeanCornerA 23 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 23 16, endpointRunWeightQ (endpointMeanCutoff 23 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 23 16) = (429376293/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 23 16 h = (logRoundedQ ((endpointMeanCutoff 23 16:ℚ)/200)).2+(429376293/1000000000000000:ℚ)+((endpointMeanRuns 23 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 23 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 23 16) r*endpointJoint24Q (endpointMeanCornerK 23 16 h) (endpointMeanCornerA 23 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 23 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 23 16 h≤endpointMeanCorner 23 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 23 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint23_16

namespace EndpointAnalyticJoint23_17
private noncomputable def weights : IntegerLookupTree := (.branch 1206 (.branch 959 (.branch 844 (.leaf (55112067000000:ℤ)) (.branch 889 (.leaf (4774953700000:ℤ)) (.leaf (6901429800000:ℤ)))) (.branch 1017 (.leaf (4997204400000:ℤ)) (.branch 1111 (.leaf (7236741200000:ℤ)) (.leaf (6037342200000:ℤ))))) (.branch 1623 (.branch 1384 (.leaf (9121809600000:ℤ)) (.branch 1507 (.leaf (4327991100000:ℤ)) (.leaf (3113371000000:ℤ)))) (.branch 2411 (.branch 1962 (.leaf (6396970000000:ℤ)) (.leaf (3612868100000:ℤ))) (.branch 3125 (.leaf (1713634900000:ℤ)) (.leaf (955719600000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 143 (.branch 127 (.leaf (1893530596968942:ℤ)) (.branch 135 (.leaf (2135024510636739:ℤ)) (.leaf (2265381169889439:ℤ)))) (.branch 152 (.leaf (2408427451425014:ℤ)) (.branch 156 (.leaf (2586760969553651:ℤ)) (.leaf (2672683052677727:ℤ))))) (.branch 183 (.branch 170 (.leaf (2786491404975565:ℤ)) (.branch 176 (.leaf (3011378107804199:ℤ)) (.leaf (3177533497270540:ℤ)))) (.branch 195 (.branch 188 (.leaf (3390322619331444:ℤ)) (.leaf (3556425916058955:ℤ))) (.branch 200 (.leaf (3811562089918661:ℤ)) (.leaf (4012080535905692:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1903407429773341:ℤ)) (.branch 135 (.leaf (2150588544360664:ℤ)) (.leaf (2284482863129168:ℤ)))) (.branch 152 (.leaf (2431770409381827:ℤ)) (.branch 156 (.leaf (2615896541991138:ℤ)) (.leaf (2704802527537502:ℤ))))) (.branch 183 (.branch 170 (.leaf (2822750232902300:ℤ)) (.branch 176 (.leaf (3056421378778847:ℤ)) (.leaf (3229562736211626:ℤ)))) (.branch 195 (.branch 188 (.leaf (3451885757299426:ℤ)) (.leaf (3625871515932628:ℤ))) (.branch 200 (.leaf (3893834262575119:ℤ)) (.leaf (4105019645221395:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1899816306560057:ℤ)) (.branch 135 (.leaf (2145799351094920:ℤ)) (.leaf (2279160579586226:ℤ)))) (.branch 152 (.leaf (2425993389134338:ℤ)) (.branch 156 (.leaf (2609787795358550:ℤ)) (.leaf (2698641705995932:ℤ))))) (.branch 183 (.branch 170 (.leaf (2816640866577361:ℤ)) (.branch 176 (.leaf (3050860737290172:ℤ)) (.leaf (3224829734122563:ℤ)))) (.branch 195 (.branch 188 (.leaf (3448792246205305:ℤ)) (.leaf (3624545964700764:ℤ))) (.branch 200 (.leaf (3896123308794026:ℤ)) (.leaf (4110963918803730:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1910098254987301:ℤ)) (.branch 135 (.leaf (2162082069545403:ℤ)) (.leaf (2299198476047744:ℤ)))) (.branch 152 (.leaf (2450553924272981:ℤ)) (.branch 156 (.leaf (2640558939792233:ℤ)) (.leaf (2732626396183613:ℤ))))) (.branch 183 (.branch 170 (.leaf (2855098841595375:ℤ)) (.branch 176 (.leaf (3098868119550432:ℤ)) (.leaf (3280483271721086:ℤ)))) (.branch 195 (.branch 188 (.leaf (3514950749394658:ℤ)) (.leaf (3699448217523322:ℤ))) (.branch 200 (.leaf (3985361556401011:ℤ)) (.leaf (4212222116452400:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 23 17) 8000 (endpointMeanRuns 23 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 23 17, EndpointRunConditions (endpointMeanCutoff 23 17) (endpointMeanBox 23 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 23 17 h) (endpointMeanCornerA 23 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 17, endpointJoint24Q (endpointMeanCornerK 23 17 h) (endpointMeanCornerA 23 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 23 17, endpointRunWeightQ (endpointMeanCutoff 23 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 23 17) = (213960209/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 23 17 h = (logRoundedQ ((endpointMeanCutoff 23 17:ℚ)/200)).2+(213960209/500000000000000:ℚ)+((endpointMeanRuns 23 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 23 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 23 17) r*endpointJoint24Q (endpointMeanCornerK 23 17 h) (endpointMeanCornerA 23 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 23 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 23 17 h≤endpointMeanCorner 23 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 23 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint23_17

namespace EndpointAnalyticJoint23_18
private noncomputable def weights : IntegerLookupTree := (.branch 1206 (.branch 959 (.branch 844 (.leaf (52793810800000:ℤ)) (.branch 889 (.leaf (4739423700000:ℤ)) (.leaf (6852228200000:ℤ)))) (.branch 1017 (.leaf (4963118800000:ℤ)) (.branch 1111 (.leaf (7189548600000:ℤ)) (.leaf (5999918200000:ℤ))))) (.branch 1623 (.branch 1384 (.leaf (9068519200000:ℤ)) (.branch 1507 (.leaf (4304202000000:ℤ)) (.leaf (3096934600000:ℤ)))) (.branch 2411 (.branch 1962 (.leaf (6365061300000:ℤ)) (.leaf (3596326200000:ℤ))) (.branch 3125 (.leaf (1706447600000:ℤ)) (.leaf (952100600000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 143 (.branch 127 (.leaf (1903407429773341:ℤ)) (.branch 135 (.leaf (2150588544360664:ℤ)) (.leaf (2284482863129168:ℤ)))) (.branch 152 (.leaf (2431770409381827:ℤ)) (.branch 156 (.leaf (2615896541991138:ℤ)) (.leaf (2704802527537502:ℤ))))) (.branch 183 (.branch 170 (.leaf (2822750232902300:ℤ)) (.branch 176 (.leaf (3056421378778847:ℤ)) (.leaf (3229562736211626:ℤ)))) (.branch 195 (.branch 188 (.leaf (3451885757299426:ℤ)) (.leaf (3625871515932628:ℤ))) (.branch 200 (.leaf (3893834262575119:ℤ)) (.leaf (4105019645221395:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1913335781061991:ℤ)) (.branch 135 (.leaf (2166266037740230:ℤ)) (.leaf (2303745621839682:ℤ)))) (.branch 152 (.leaf (2455339611930669:ℤ)) (.branch 156 (.leaf (2645360278333702:ℤ)) (.leaf (2737308004270650:ℤ))))) (.branch 183 (.branch 170 (.leaf (2859480873733342:ℤ)) (.branch 176 (.leaf (3102138393198344:ℤ)) (.leaf (3282443906912716:ℤ)))) (.branch 195 (.branch 188 (.leaf (3514566788866938:ℤ)) (.leaf (3696673165800204:ℤ))) (.branch 200 (.leaf (3977882271551166:ℤ)) (.leaf (4200111671948182:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1910098254987301:ℤ)) (.branch 135 (.leaf (2162082069545403:ℤ)) (.leaf (2299198476047744:ℤ)))) (.branch 152 (.leaf (2450553924272981:ℤ)) (.branch 156 (.leaf (2640558939792233:ℤ)) (.leaf (2732626396183613:ℤ))))) (.branch 183 (.branch 170 (.leaf (2855098841595375:ℤ)) (.branch 176 (.leaf (3098868119550432:ℤ)) (.leaf (3280483271721086:ℤ)))) (.branch 195 (.branch 188 (.leaf (3514950749394658:ℤ)) (.leaf (3699448217523322:ℤ))) (.branch 200 (.leaf (3985361556401011:ℤ)) (.leaf (4212222116452400:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1920435850091067:ℤ)) (.branch 135 (.leaf (2178488344245450:ℤ)) (.leaf (2319412541445411:ℤ)))) (.branch 152 (.leaf (2475363108022541:ℤ)) (.branch 156 (.leaf (2671692896609147:ℤ)) (.leaf (2767039064329465:ℤ))))) (.branch 183 (.branch 170 (.leaf (2894081915805140:ℤ)) (.branch 176 (.leaf (3147630930835463:ℤ)) (.leaf (3337097268166307:ℤ)))) (.branch 195 (.branch 188 (.leaf (3582378377318641:ℤ)) (.leaf (3775898346281933:ℤ))) (.branch 200 (.leaf (4076643749798411:ℤ)) (.leaf (4315974430515991:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 23 18) 8000 (endpointMeanRuns 23 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 23 18, EndpointRunConditions (endpointMeanCutoff 23 18) (endpointMeanBox 23 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 23 18 h) (endpointMeanCornerA 23 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 18, endpointJoint24Q (endpointMeanCornerK 23 18 h) (endpointMeanCornerA 23 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 23 18, endpointRunWeightQ (endpointMeanCutoff 23 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 23 18) = (213343507/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 23 18 h = (logRoundedQ ((endpointMeanCutoff 23 18:ℚ)/200)).2+(213343507/500000000000000:ℚ)+((endpointMeanRuns 23 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 23 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 23 18) r*endpointJoint24Q (endpointMeanCornerK 23 18 h) (endpointMeanCornerA 23 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 23 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 23 18 h≤endpointMeanCorner 23 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 23 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint23_18

namespace EndpointAnalyticJoint23_19
private noncomputable def weights : IntegerLookupTree := (.branch 1384 (.branch 1017 (.branch 844 (.leaf (50187885400000:ℤ)) (.branch 908 (.leaf (6724448200000:ℤ)) (.leaf (10272461000000:ℤ)))) (.branch 1111 (.leaf (7135122100000:ℤ)) (.branch 1206 (.leaf (5956757800000:ℤ)) (.leaf (9007060300000:ℤ))))) (.branch 1962 (.branch 1507 (.leaf (4276766300000:ℤ)) (.branch 1623 (.leaf (3077978800000:ℤ)) (.leaf (6328261500000:ℤ)))) (.branch 2411 (.leaf (3577248600000:ℤ)) (.branch 3125 (.leaf (1698158500000:ℤ)) (.leaf (947927000000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 143 (.branch 127 (.leaf (1913335781061991:ℤ)) (.branch 135 (.leaf (2166266037740230:ℤ)) (.leaf (2303745621839682:ℤ)))) (.branch 152 (.leaf (2455339611930669:ℤ)) (.branch 156 (.leaf (2645360278333702:ℤ)) (.leaf (2737308004270650:ℤ))))) (.branch 183 (.branch 170 (.leaf (2859480873733342:ℤ)) (.branch 176 (.leaf (3102138393198344:ℤ)) (.leaf (3282443906912716:ℤ)))) (.branch 193 (.leaf (3514566788866938:ℤ)) (.branch 200 (.leaf (3894168157023807:ℤ)) (.leaf (4200111671948182:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1923315919560130:ℤ)) (.branch 135 (.leaf (2182057817880653:ℤ)) (.leaf (2323170804124968:ℤ)))) (.branch 152 (.leaf (2479137251879131:ℤ)) (.branch 156 (.leaf (2675155874803501:ℤ)) (.leaf (2770204121727806:ℤ))))) (.branch 183 (.branch 170 (.leaf (2896689466867831:ℤ)) (.branch 176 (.leaf (3148539228710685:ℤ)) (.leaf (3336190958986337:ℤ)))) (.branch 193 (.leaf (3578386013293245:ℤ)) (.branch 200 (.leaf (3975864463755370:ℤ)) (.leaf (4297406488022761:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1920435850091067:ℤ)) (.branch 135 (.leaf (2178488344245450:ℤ)) (.leaf (2319412541445411:ℤ)))) (.branch 152 (.leaf (2475363108022541:ℤ)) (.branch 156 (.leaf (2671692896609147:ℤ)) (.leaf (2767039064329465:ℤ))))) (.branch 183 (.branch 170 (.leaf (2894081915805140:ℤ)) (.branch 176 (.leaf (3147630930835463:ℤ)) (.leaf (3337097268166307:ℤ)))) (.branch 193 (.leaf (3582378377318641:ℤ)) (.branch 200 (.leaf (3986869472832881:ℤ)) (.leaf (4315974430515991:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1930829393035343:ℤ)) (.branch 135 (.leaf (2195019112762512:ℤ)) (.leaf (2339804324619142:ℤ)))) (.branch 152 (.leaf (2500423457678808:ℤ)) (.branch 156 (.leaf (2703193943610059:ℤ)) (.leaf (2801885100070158:ℤ))))) (.branch 183 (.branch 170 (.leaf (2933597258829104:ℤ)) (.branch 176 (.leaf (3197161058338123:ℤ)) (.leaf (3394688298886057:ℤ)))) (.branch 193 (.leaf (3651099475715351:ℤ)) (.branch 200 (.leaf (4075553895830804:ℤ)) (.leaf (4422282294210148:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 23 19) 8000 (endpointMeanRuns 23 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 23 19, EndpointRunConditions (endpointMeanCutoff 23 19) (endpointMeanBox 23 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 23 19 h) (endpointMeanCornerA 23 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 19, endpointJoint24Q (endpointMeanCornerK 23 19 h) (endpointMeanCornerA 23 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 23 19, endpointRunWeightQ (endpointMeanCutoff 23 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 23 19) = (106316137/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 23 19 h = (logRoundedQ ((endpointMeanCutoff 23 19:ℚ)/200)).2+(106316137/250000000000000:ℚ)+((endpointMeanRuns 23 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 23 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 23 19) r*endpointJoint24Q (endpointMeanCornerK 23 19 h) (endpointMeanCornerA 23 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 23 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 23 19 h≤endpointMeanCorner 23 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 23 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint23_19

namespace EndpointAnalyticJoint23_20
private noncomputable def weights : IntegerLookupTree := (.branch 1206 (.branch 908 (.branch 844 (.leaf (47684249400000:ℤ)) (.leaf (6666916500000:ℤ))) (.branch 1017 (.leaf (10189846700000:ℤ)) (.branch 1111 (.leaf (7081359900000:ℤ)) (.leaf (5914124200000:ℤ))))) (.branch 1962 (.branch 1384 (.leaf (8946351500000:ℤ)) (.branch 1623 (.leaf (7967137500000:ℤ)) (.leaf (6291910800000:ℤ)))) (.branch 2411 (.leaf (3558403900000:ℤ)) (.branch 3125 (.leaf (1689970600000:ℤ)) (.leaf (943804200000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 135 (.branch 127 (.leaf (1923315919560130:ℤ)) (.leaf (2182057817880653:ℤ))) (.branch 143 (.leaf (2323170804124968:ℤ)) (.branch 152 (.leaf (2479137251879131:ℤ)) (.leaf (2675155874803501:ℤ))))) (.branch 183 (.branch 170 (.leaf (2896689466867831:ℤ)) (.branch 176 (.leaf (3148539228710685:ℤ)) (.leaf (3336190958986337:ℤ)))) (.branch 193 (.leaf (3578386013293245:ℤ)) (.branch 200 (.leaf (3975864463755370:ℤ)) (.leaf (4297406488022761:ℤ)))))), (.branch 161 (.branch 135 (.branch 127 (.leaf (1933348115394694:ℤ)) (.leaf (2197964717916625:ℤ))) (.branch 143 (.leaf (2342759779540552:ℤ)) (.branch 152 (.leaf (2503165543287927:ℤ)) (.leaf (2705287069254514:ℤ))))) (.branch 183 (.branch 170 (.leaf (2934382231592958:ℤ)) (.branch 176 (.leaf (3195634113702243:ℤ)) (.leaf (3390818070457324:ℤ)))) (.branch 193 (.leaf (3643364098441533:ℤ)) (.branch 200 (.leaf (4059274688906593:ℤ)) (.leaf (4396955120656136:ℤ)))))), (.branch 161 (.branch 135 (.branch 127 (.leaf (1930829393035343:ℤ)) (.leaf (2195019112762512:ℤ))) (.branch 143 (.leaf (2339804324619142:ℤ)) (.branch 152 (.leaf (2500423457678808:ℤ)) (.leaf (2703193943610059:ℤ))))) (.branch 183 (.branch 170 (.leaf (2933597258829104:ℤ)) (.branch 176 (.leaf (3197161058338123:ℤ)) (.leaf (3394688298886057:ℤ)))) (.branch 193 (.leaf (3651099475715351:ℤ)) (.branch 200 (.leaf (4075553895830804:ℤ)) (.leaf (4422282294210148:ℤ)))))), (.branch 161 (.branch 135 (.branch 127 (.leaf (1941279186614041:ℤ)) (.leaf (2211675319778464:ℤ))) (.branch 143 (.leaf (2360375388025940:ℤ)) (.branch 152 (.leaf (2525737516022442:ℤ)) (.leaf (2735066409033885:ℤ))))) (.branch 183 (.branch 170 (.leaf (2973652138182636:ℤ)) (.branch 176 (.leaf (3247470576304381:ℤ)) (.leaf (3453273225363954:ℤ)))) (.branch 193 (.leaf (3721138857349471:ℤ)) (.branch 200 (.leaf (4166211026221351:ℤ)) (.leaf (4531208653927662:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 23 20) 8000 (endpointMeanRuns 23 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 23 20, EndpointRunConditions (endpointMeanCutoff 23 20) (endpointMeanBox 23 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 23 20 h) (endpointMeanCornerA 23 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 20, endpointJoint24Q (endpointMeanCornerK 23 20 h) (endpointMeanCornerA 23 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 23 20, endpointRunWeightQ (endpointMeanCutoff 23 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 23 20) = (211929723/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 23 20 h = (logRoundedQ ((endpointMeanCutoff 23 20:ℚ)/200)).2+(211929723/500000000000000:ℚ)+((endpointMeanRuns 23 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 23 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 23 20) r*endpointJoint24Q (endpointMeanCornerK 23 20 h) (endpointMeanCornerA 23 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 23 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 23 20 h≤endpointMeanCorner 23 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 23 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint23_20

namespace EndpointAnalyticJoint23_21
private noncomputable def weights : IntegerLookupTree := (.branch 1206 (.branch 928 (.branch 844 (.leaf (45278863700000:ℤ)) (.leaf (8725731200000:ℤ))) (.branch 1055 (.leaf (11355653200000:ℤ)) (.leaf (10436578000000:ℤ)))) (.branch 1623 (.branch 1384 (.leaf (8886374800000:ℤ)) (.leaf (7917719100000:ℤ))) (.branch 1962 (.leaf (6255998500000:ℤ)) (.branch 3125 (.leaf (7107602400000:ℤ)) (.leaf (939731200000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 143 (.branch 127 (.leaf (1933348115394694:ℤ)) (.leaf (2197964717916625:ℤ))) (.branch 152 (.leaf (2503165543287927:ℤ)) (.leaf (2705287069254514:ℤ)))) (.branch 180 (.branch 170 (.leaf (2934382231592958:ℤ)) (.leaf (3195634113702243:ℤ))) (.branch 191 (.leaf (3531611930351173:ℤ)) (.branch 200 (.leaf (3970281200129048:ℤ)) (.leaf (4396955120656136:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1943432640101616:ℤ)) (.leaf (2213987577056286:ℤ))) (.branch 152 (.leaf (2527426721676899:ℤ)) (.leaf (2735757641641440:ℤ)))) (.branch 180 (.branch 170 (.leaf (2972565468123534:ℤ)) (.leaf (3243433429552444:ℤ))) (.branch 191 (.leaf (3592975913616353:ℤ)) (.branch 200 (.leaf (4051226335197255:ℤ)) (.leaf (4498809779095254:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1941279186614041:ℤ)) (.leaf (2211675319778464:ℤ))) (.branch 152 (.leaf (2525737516022442:ℤ)) (.leaf (2735066409033885:ℤ)))) (.branch 180 (.branch 170 (.leaf (2973652138182636:ℤ)) (.leaf (3247470576304381:ℤ))) (.branch 191 (.leaf (3602386723909942:ℤ)) (.branch 200 (.leaf (4070563369339178:ℤ)) (.leaf (4531208653927662:ℤ)))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1951785535259816:ℤ)) (.leaf (2228457917143620:ℤ))) (.branch 152 (.leaf (2551307851576980:ℤ)) (.leaf (2767314672152352:ℤ)))) (.branch 180 (.branch 170 (.leaf (3014253920610604:ℤ)) (.leaf (3298571748976742:ℤ))) (.branch 191 (.leaf (3668445018287120:ℤ)) (.branch 200 (.leaf (4158489690511070:ℤ)) (.leaf (4642818006509933:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 23 21) 8000 (endpointMeanRuns 23 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 23 21, EndpointRunConditions (endpointMeanCutoff 23 21) (endpointMeanBox 23 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 23 21 h) (endpointMeanCornerA 23 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 21, endpointJoint24Q (endpointMeanCornerK 23 21 h) (endpointMeanCornerA 23 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 23 21, endpointRunWeightQ (endpointMeanCutoff 23 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 23 21) = (422471287/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 23 21 h = (logRoundedQ ((endpointMeanCutoff 23 21:ℚ)/200)).2+(422471287/1000000000000000:ℚ)+((endpointMeanRuns 23 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 23 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 23 21) r*endpointJoint24Q (endpointMeanCornerK 23 21 h) (endpointMeanCornerA 23 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 23 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 23 21 h≤endpointMeanCorner 23 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 23 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint23_21

namespace EndpointAnalyticJoint23_22
private noncomputable def weights : IntegerLookupTree := (.branch 1384 (.branch 1055 (.branch 844 (.leaf (43292366200000:ℤ)) (.leaf (22321439700000:ℤ))) (.branch 1206 (.leaf (10371995600000:ℤ)) (.leaf (8835535700000:ℤ)))) (.branch 1962 (.branch 1623 (.leaf (7875829600000:ℤ)) (.leaf (6225557500000:ℤ))) (.branch 3125 (.leaf (7076571500000:ℤ)) (.leaf (936278700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 161 (.branch 143 (.branch 127 (.leaf (1943432640101616:ℤ)) (.leaf (2213987577056286:ℤ))) (.branch 152 (.leaf (2527426721676899:ℤ)) (.leaf (2735757641641440:ℤ)))) (.branch 180 (.branch 170 (.leaf (2972565468123534:ℤ)) (.leaf (3243433429552444:ℤ))) (.branch 200 (.leaf (3592975913616353:ℤ)) (.leaf (4498809779095254:ℤ))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1953569766633196:ℤ)) (.leaf (2230127240625477:ℤ))) (.branch 152 (.leaf (2551923044232983:ℤ)) (.leaf (2766571414493912:ℤ)))) (.branch 180 (.branch 170 (.leaf (3011245558655012:ℤ)) (.leaf (3291947712922220:ℤ))) (.branch 200 (.leaf (3655406134768490:ℤ)) (.leaf (4603023882004710:ℤ))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1951785535259816:ℤ)) (.leaf (2228457917143620:ℤ))) (.branch 152 (.leaf (2551307851576980:ℤ)) (.leaf (2767314672152352:ℤ)))) (.branch 180 (.branch 170 (.leaf (3014253920610604:ℤ)) (.leaf (3298571748976742:ℤ))) (.branch 200 (.leaf (3668445018287120:ℤ)) (.leaf (4642818006509933:ℤ))))), (.branch 161 (.branch 143 (.branch 127 (.leaf (1962348745052937:ℤ)) (.leaf (2245367863931087:ℤ))) (.branch 152 (.leaf (2577137058869473:ℤ)) (.leaf (2799943163871752:ℤ)))) (.branch 180 (.branch 170 (.leaf (3055410073442280:ℤ)) (.leaf (3350477033583959:ℤ))) (.branch 200 (.leaf (3735714647979039:ℤ)) (.leaf (4757176437436466:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 23 22) 8000 (endpointMeanRuns 23 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 23 22, EndpointRunConditions (endpointMeanCutoff 23 22) (endpointMeanBox 23 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 23 22 h) (endpointMeanCornerA 23 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 23 22, endpointJoint24Q (endpointMeanCornerK 23 22 h) (endpointMeanCornerA 23 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 23 22, endpointRunWeightQ (endpointMeanCutoff 23 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 23 22) = (421294617/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 23 22 h = (logRoundedQ ((endpointMeanCutoff 23 22:ℚ)/200)).2+(421294617/1000000000000000:ℚ)+((endpointMeanRuns 23 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 23 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 23 22) r*endpointJoint24Q (endpointMeanCornerK 23 22 h) (endpointMeanCornerA 23 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 23 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 23 22 h≤endpointMeanCorner 23 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 23 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint23_22

private theorem activeIndices18 : ∀ai : Fin 42, endpointMeanActive 18 ai → ai∈
    ([4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow18 (ai : Fin 42) : endpointMeanActive 18 ai →
    EndpointJointNumericalConditions 18 ai := by
  intro hact
  have hi := activeIndices18 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint18_04.conditions
  · exact EndpointAnalyticJoint18_05.conditions
  · exact EndpointAnalyticJoint18_06.conditions
  · exact EndpointAnalyticJoint18_07.conditions
  · exact EndpointAnalyticJoint18_08.conditions
  · exact EndpointAnalyticJoint18_09.conditions
  · exact EndpointAnalyticJoint18_10.conditions
  · exact EndpointAnalyticJoint18_11.conditions
  · exact EndpointAnalyticJoint18_12.conditions
  · exact EndpointAnalyticJoint18_13.conditions
  · exact EndpointAnalyticJoint18_14.conditions
  · exact EndpointAnalyticJoint18_15.conditions
  · exact EndpointAnalyticJoint18_16.conditions
  · exact EndpointAnalyticJoint18_17.conditions
  · exact EndpointAnalyticJoint18_18.conditions
  · exact EndpointAnalyticJoint18_19.conditions

private theorem activeIndices19 : ∀ai : Fin 42, endpointMeanActive 19 ai → ai∈
    ([4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow19 (ai : Fin 42) : endpointMeanActive 19 ai →
    EndpointJointNumericalConditions 19 ai := by
  intro hact
  have hi := activeIndices19 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint19_04.conditions
  · exact EndpointAnalyticJoint19_05.conditions
  · exact EndpointAnalyticJoint19_06.conditions
  · exact EndpointAnalyticJoint19_07.conditions
  · exact EndpointAnalyticJoint19_08.conditions
  · exact EndpointAnalyticJoint19_09.conditions
  · exact EndpointAnalyticJoint19_10.conditions
  · exact EndpointAnalyticJoint19_11.conditions
  · exact EndpointAnalyticJoint19_12.conditions
  · exact EndpointAnalyticJoint19_13.conditions
  · exact EndpointAnalyticJoint19_14.conditions
  · exact EndpointAnalyticJoint19_15.conditions
  · exact EndpointAnalyticJoint19_16.conditions
  · exact EndpointAnalyticJoint19_17.conditions
  · exact EndpointAnalyticJoint19_18.conditions
  · exact EndpointAnalyticJoint19_19.conditions
  · exact EndpointAnalyticJoint19_20.conditions

private theorem activeIndices20 : ∀ai : Fin 42, endpointMeanActive 20 ai → ai∈
    ([5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow20 (ai : Fin 42) : endpointMeanActive 20 ai →
    EndpointJointNumericalConditions 20 ai := by
  intro hact
  have hi := activeIndices20 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint20_05.conditions
  · exact EndpointAnalyticJoint20_06.conditions
  · exact EndpointAnalyticJoint20_07.conditions
  · exact EndpointAnalyticJoint20_08.conditions
  · exact EndpointAnalyticJoint20_09.conditions
  · exact EndpointAnalyticJoint20_10.conditions
  · exact EndpointAnalyticJoint20_11.conditions
  · exact EndpointAnalyticJoint20_12.conditions
  · exact EndpointAnalyticJoint20_13.conditions
  · exact EndpointAnalyticJoint20_14.conditions
  · exact EndpointAnalyticJoint20_15.conditions
  · exact EndpointAnalyticJoint20_16.conditions
  · exact EndpointAnalyticJoint20_17.conditions
  · exact EndpointAnalyticJoint20_18.conditions
  · exact EndpointAnalyticJoint20_19.conditions
  · exact EndpointAnalyticJoint20_20.conditions

private theorem activeIndices21 : ∀ai : Fin 42, endpointMeanActive 21 ai → ai∈
    ([5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow21 (ai : Fin 42) : endpointMeanActive 21 ai →
    EndpointJointNumericalConditions 21 ai := by
  intro hact
  have hi := activeIndices21 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint21_05.conditions
  · exact EndpointAnalyticJoint21_06.conditions
  · exact EndpointAnalyticJoint21_07.conditions
  · exact EndpointAnalyticJoint21_08.conditions
  · exact EndpointAnalyticJoint21_09.conditions
  · exact EndpointAnalyticJoint21_10.conditions
  · exact EndpointAnalyticJoint21_11.conditions
  · exact EndpointAnalyticJoint21_12.conditions
  · exact EndpointAnalyticJoint21_13.conditions
  · exact EndpointAnalyticJoint21_14.conditions
  · exact EndpointAnalyticJoint21_15.conditions
  · exact EndpointAnalyticJoint21_16.conditions
  · exact EndpointAnalyticJoint21_17.conditions
  · exact EndpointAnalyticJoint21_18.conditions
  · exact EndpointAnalyticJoint21_19.conditions
  · exact EndpointAnalyticJoint21_20.conditions
  · exact EndpointAnalyticJoint21_21.conditions

private theorem activeIndices22 : ∀ai : Fin 42, endpointMeanActive 22 ai → ai∈
    ([5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow22 (ai : Fin 42) : endpointMeanActive 22 ai →
    EndpointJointNumericalConditions 22 ai := by
  intro hact
  have hi := activeIndices22 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint22_05.conditions
  · exact EndpointAnalyticJoint22_06.conditions
  · exact EndpointAnalyticJoint22_07.conditions
  · exact EndpointAnalyticJoint22_08.conditions
  · exact EndpointAnalyticJoint22_09.conditions
  · exact EndpointAnalyticJoint22_10.conditions
  · exact EndpointAnalyticJoint22_11.conditions
  · exact EndpointAnalyticJoint22_12.conditions
  · exact EndpointAnalyticJoint22_13.conditions
  · exact EndpointAnalyticJoint22_14.conditions
  · exact EndpointAnalyticJoint22_15.conditions
  · exact EndpointAnalyticJoint22_16.conditions
  · exact EndpointAnalyticJoint22_17.conditions
  · exact EndpointAnalyticJoint22_18.conditions
  · exact EndpointAnalyticJoint22_19.conditions
  · exact EndpointAnalyticJoint22_20.conditions
  · exact EndpointAnalyticJoint22_21.conditions

private theorem activeIndices23 : ∀ai : Fin 42, endpointMeanActive 23 ai → ai∈
    ([6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow23 (ai : Fin 42) : endpointMeanActive 23 ai →
    EndpointJointNumericalConditions 23 ai := by
  intro hact
  have hi := activeIndices23 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint23_06.conditions
  · exact EndpointAnalyticJoint23_07.conditions
  · exact EndpointAnalyticJoint23_08.conditions
  · exact EndpointAnalyticJoint23_09.conditions
  · exact EndpointAnalyticJoint23_10.conditions
  · exact EndpointAnalyticJoint23_11.conditions
  · exact EndpointAnalyticJoint23_12.conditions
  · exact EndpointAnalyticJoint23_13.conditions
  · exact EndpointAnalyticJoint23_14.conditions
  · exact EndpointAnalyticJoint23_15.conditions
  · exact EndpointAnalyticJoint23_16.conditions
  · exact EndpointAnalyticJoint23_17.conditions
  · exact EndpointAnalyticJoint23_18.conditions
  · exact EndpointAnalyticJoint23_19.conditions
  · exact EndpointAnalyticJoint23_20.conditions
  · exact EndpointAnalyticJoint23_21.conditions
  · exact EndpointAnalyticJoint23_22.conditions

end SingularValueBounds.KL.Certificates
