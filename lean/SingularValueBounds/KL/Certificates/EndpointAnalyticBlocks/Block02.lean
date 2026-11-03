import SingularValueBounds.KL.Certificates.EndpointAnalyticLogs
import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SingularValueBounds.KL.Certificates

namespace EndpointAnalyticJoint12_02
private noncomputable def weights : IntegerLookupTree := (.branch 1631 (.branch 1125 (.leaf (154707120000000:ℤ)) (.leaf (19099432100000:ℤ))) (.branch 2813 (.leaf (11667356900000:ℤ)) (.leaf (1744401200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 169 (.branch 140 (.leaf (1785129621650707:ℤ)) (.leaf (2043780704991205:ℤ))) (.branch 200 (.leaf (2380782987945786:ℤ)) (.leaf (2809007562635658:ℤ)))), (.branch 169 (.branch 140 (.leaf (1788044027818037:ℤ)) (.leaf (2048986675861439:ℤ))) (.branch 200 (.leaf (2389978754784980:ℤ)) (.leaf (2824903231995377:ℤ)))), (.branch 169 (.branch 140 (.leaf (1785820274469911:ℤ)) (.leaf (2045096277153526:ℤ))) (.branch 200 (.leaf (2383285189269859:ℤ)) (.leaf (2813703571299324:ℤ)))), (.branch 169 (.branch 140 (.leaf (1788854734902343:ℤ)) (.leaf (2050532374496164:ℤ))) (.branch 200 (.leaf (2392922613623395:ℤ)) (.leaf (2830438303131011:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 12 2) 8000 (endpointMeanRuns 12 2) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 12 2, EndpointRunConditions (endpointMeanCutoff 12 2) (endpointMeanBox 12 2).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 2, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 12 2 h) (endpointMeanCornerA 12 2 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 2, endpointJoint24Q (endpointMeanCornerK 12 2 h) (endpointMeanCornerA 12 2 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 12 2, endpointRunWeightQ (endpointMeanCutoff 12 2) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 12 2) = (45959971/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 12 2 h = (logRoundedQ ((endpointMeanCutoff 12 2:ℚ)/200)).2+(45959971/100000000000000:ℚ)+((endpointMeanRuns 12 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 12 2).map (fun r => endpointRunWeightQ (endpointMeanCutoff 12 2) r*endpointJoint24Q (endpointMeanCornerK 12 2 h) (endpointMeanCornerA 12 2 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 12 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 12 2 h≤endpointMeanCorner 12 2 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 12 2 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint12_02

namespace EndpointAnalyticJoint12_03
private noncomputable def weights : IntegerLookupTree := (.branch 1631 (.branch 1125 (.leaf (151225592800000:ℤ)) (.leaf (19014335900000:ℤ))) (.branch 2813 (.leaf (11623308100000:ℤ)) (.leaf (1738940200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 169 (.branch 140 (.leaf (1788044027818037:ℤ)) (.leaf (2048986675861439:ℤ))) (.branch 200 (.leaf (2389978754784980:ℤ)) (.leaf (2824903231995377:ℤ)))), (.branch 169 (.branch 140 (.leaf (1794685385739962:ℤ)) (.leaf (2060867798104510:ℤ))) (.branch 200 (.leaf (2411010535428637:ℤ)) (.leaf (2861365084220703:ℤ)))), (.branch 169 (.branch 140 (.leaf (1788854734902343:ℤ)) (.leaf (2050532374496164:ℤ))) (.branch 200 (.leaf (2392922613623395:ℤ)) (.leaf (2830438303131011:ℤ)))), (.branch 169 (.branch 140 (.leaf (1795770425459695:ℤ)) (.leaf (2062940940579362:ℤ))) (.branch 200 (.leaf (2414971034439258:ℤ)) (.leaf (2868842876230053:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 12 3) 8000 (endpointMeanRuns 12 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 12 3, EndpointRunConditions (endpointMeanCutoff 12 3) (endpointMeanBox 12 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 12 3 h) (endpointMeanCornerA 12 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 3, endpointJoint24Q (endpointMeanCornerK 12 3 h) (endpointMeanCornerA 12 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 12 3, endpointRunWeightQ (endpointMeanCutoff 12 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 12 3) = (458516251/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 12 3 h = (logRoundedQ ((endpointMeanCutoff 12 3:ℚ)/200)).2+(458516251/1000000000000000:ℚ)+((endpointMeanRuns 12 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 12 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 12 3) r*endpointJoint24Q (endpointMeanCornerK 12 3 h) (endpointMeanCornerA 12 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 12 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 12 3 h≤endpointMeanCorner 12 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 12 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint12_03

namespace EndpointAnalyticJoint12_04
private noncomputable def weights : IntegerLookupTree := (.branch 1631 (.branch 1125 (.leaf (146985511200000:ℤ)) (.leaf (18909079600000:ℤ))) (.branch 2813 (.leaf (11568823700000:ℤ)) (.leaf (1732185300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 169 (.branch 140 (.leaf (1794685385739962:ℤ)) (.leaf (2060867798104510:ℤ))) (.branch 200 (.leaf (2411010535428637:ℤ)) (.leaf (2861365084220703:ℤ)))), (.branch 169 (.branch 140 (.leaf (1801351411754144:ℤ)) (.leaf (2072817813458221:ℤ))) (.branch 200 (.leaf (2432227395456848:ℤ)) (.leaf (2898297560236838:ℤ)))), (.branch 169 (.branch 140 (.leaf (1795770425459695:ℤ)) (.leaf (2062940940579362:ℤ))) (.branch 200 (.leaf (2414971034439258:ℤ)) (.leaf (2868842876230053:ℤ)))), (.branch 169 (.branch 140 (.leaf (1802712851992275:ℤ)) (.leaf (2075424595704875:ℤ))) (.branch 200 (.leaf (2437222609698017:ℤ)) (.leaf (2907768538671797:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 12 4) 8000 (endpointMeanRuns 12 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 12 4, EndpointRunConditions (endpointMeanCutoff 12 4) (endpointMeanBox 12 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 12 4 h) (endpointMeanCornerA 12 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 4, endpointJoint24Q (endpointMeanCornerK 12 4 h) (endpointMeanCornerA 12 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 12 4, endpointRunWeightQ (endpointMeanCutoff 12 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 12 4) = (457176113/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 12 4 h = (logRoundedQ ((endpointMeanCutoff 12 4:ℚ)/200)).2+(457176113/1000000000000000:ℚ)+((endpointMeanRuns 12 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 12 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 12 4) r*endpointJoint24Q (endpointMeanCornerK 12 4 h) (endpointMeanCornerA 12 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 12 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 12 4 h≤endpointMeanCorner 12 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 12 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint12_04

namespace EndpointAnalyticJoint12_05
private noncomputable def weights : IntegerLookupTree := (.branch 1631 (.branch 1125 (.leaf (142056369400000:ℤ)) (.leaf (18784368600000:ℤ))) (.branch 2813 (.leaf (11504268900000:ℤ)) (.leaf (1724182000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 169 (.branch 140 (.leaf (1801351411754144:ℤ)) (.leaf (2072817813458221:ℤ))) (.branch 200 (.leaf (2432227395456848:ℤ)) (.leaf (2898297560236838:ℤ)))), (.branch 169 (.branch 140 (.leaf (1808042197485646:ℤ)) (.leaf (2084837121401721:ℤ))) (.branch 200 (.leaf (2453630963565691:ℤ)) (.leaf (2935706734522691:ℤ)))), (.branch 169 (.branch 140 (.leaf (1802712851992275:ℤ)) (.leaf (2075424595704875:ℤ))) (.branch 200 (.leaf (2437222609698017:ℤ)) (.leaf (2907768538671797:ℤ)))), (.branch 169 (.branch 140 (.leaf (1809682117861041:ℤ)) (.leaf (2087983794265603:ℤ))) (.branch 200 (.leaf (2459679211267422:ℤ)) (.leaf (2947222360814818:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 12 5) 8000 (endpointMeanRuns 12 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 12 5, EndpointRunConditions (endpointMeanCutoff 12 5) (endpointMeanBox 12 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 12 5 h) (endpointMeanCornerA 12 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 5, endpointJoint24Q (endpointMeanCornerK 12 5 h) (endpointMeanCornerA 12 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 12 5, endpointRunWeightQ (endpointMeanCutoff 12 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 12 5) = (28474267/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 12 5 h = (logRoundedQ ((endpointMeanCutoff 12 5:ℚ)/200)).2+(28474267/62500000000000:ℚ)+((endpointMeanRuns 12 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 12 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 12 5) r*endpointJoint24Q (endpointMeanCornerK 12 5 h) (endpointMeanCornerA 12 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 12 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 12 5 h≤endpointMeanCorner 12 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 12 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint12_05

namespace EndpointAnalyticJoint12_06
private noncomputable def weights : IntegerLookupTree := (.branch 1279 (.branch 1125 (.leaf (138076877400000:ℤ)) (.leaf (5534767300000:ℤ))) (.branch 1631 (.leaf (8927017000000:ℤ)) (.branch 2813 (.leaf (11451145100000:ℤ)) (.leaf (1717595800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 169 (.branch 140 (.leaf (1808042197485646:ℤ)) (.leaf (2084837121401721:ℤ))) (.branch 188 (.leaf (2453630963565691:ℤ)) (.branch 200 (.leaf (2736879770264244:ℤ)) (.leaf (2935706734522691:ℤ))))), (.branch 169 (.branch 140 (.leaf (1814757834899843:ℤ)) (.leaf (2096926123730570:ℤ))) (.branch 188 (.leaf (2475222882783750:ℤ)) (.branch 200 (.leaf (2767529149825869:ℤ)) (.leaf (2973598759962250:ℤ))))), (.branch 169 (.branch 140 (.leaf (1809682117861041:ℤ)) (.leaf (2087983794265603:ℤ))) (.branch 188 (.leaf (2459679211267422:ℤ)) (.branch 200 (.leaf (2745901264503070:ℤ)) (.leaf (2947222360814818:ℤ))))), (.branch 169 (.branch 140 (.leaf (1816678326826540:ℤ)) (.leaf (2100618993404146:ℤ))) (.branch 188 (.leaf (2482342728262620:ℤ)) (.branch 200 (.leaf (2778175013995776:ℤ)) (.leaf (2987211508951295:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 12 6) 8000 (endpointMeanRuns 12 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 12 6, EndpointRunConditions (endpointMeanCutoff 12 6) (endpointMeanBox 12 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 12 6 h) (endpointMeanCornerA 12 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 6, endpointJoint24Q (endpointMeanCornerK 12 6 h) (endpointMeanCornerA 12 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 12 6, endpointRunWeightQ (endpointMeanCutoff 12 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 12 6) = (141963/312500000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 12 6 h = (logRoundedQ ((endpointMeanCutoff 12 6:ℚ)/200)).2+(141963/312500000000:ℚ)+((endpointMeanRuns 12 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 12 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 12 6) r*endpointJoint24Q (endpointMeanCornerK 12 6 h) (endpointMeanCornerA 12 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 12 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 12 6 h≤endpointMeanCorner 12 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 12 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint12_06

namespace EndpointAnalyticJoint12_07
private noncomputable def weights : IntegerLookupTree := (.branch 1279 (.branch 1125 (.leaf (134210065700000:ℤ)) (.leaf (5503535700000:ℤ))) (.branch 1631 (.leaf (8880564000000:ℤ)) (.branch 2813 (.leaf (11398617600000:ℤ)) (.leaf (1711083600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 169 (.branch 140 (.leaf (1814757834899843:ℤ)) (.leaf (2096926123730570:ℤ))) (.branch 188 (.leaf (2475222882783750:ℤ)) (.branch 200 (.leaf (2767529149825869:ℤ)) (.leaf (2973598759962250:ℤ))))), (.branch 169 (.branch 140 (.leaf (1821498416303695:ℤ)) (.leaf (2109085224570140:ℤ))) (.branch 188 (.leaf (2497004810598228:ℤ)) (.branch 200 (.leaf (2798521761296223:ℤ)) (.leaf (3011979868856579:ℤ))))), (.branch 169 (.branch 140 (.leaf (1816678326826540:ℤ)) (.leaf (2100618993404146:ℤ))) (.branch 188 (.leaf (2482342728262620:ℤ)) (.branch 200 (.leaf (2778175013995776:ℤ)) (.leaf (2987211508951295:ℤ))))), (.branch 169 (.branch 140 (.leaf (1823701583050451:ℤ)) (.leaf (2113330653029455:ℤ))) (.branch 188 (.leaf (2505215067205106:ℤ)) (.branch 200 (.leaf (2810828090640474:ℤ)) (.leaf (3027743246608649:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 12 7) 8000 (endpointMeanRuns 12 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 12 7, EndpointRunConditions (endpointMeanCutoff 12 7) (endpointMeanBox 12 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 12 7 h) (endpointMeanCornerA 12 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 7, endpointJoint24Q (endpointMeanCornerK 12 7 h) (endpointMeanCornerA 12 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 12 7, endpointRunWeightQ (endpointMeanCutoff 12 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 12 7) = (452989593/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 12 7 h = (logRoundedQ ((endpointMeanCutoff 12 7:ℚ)/200)).2+(452989593/1000000000000000:ℚ)+((endpointMeanRuns 12 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 12 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 12 7) r*endpointJoint24Q (endpointMeanCornerK 12 7 h) (endpointMeanCornerA 12 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 12 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 12 7 h≤endpointMeanCorner 12 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 12 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint12_07

namespace EndpointAnalyticJoint12_08
private noncomputable def weights : IntegerLookupTree := (.branch 1631 (.branch 1125 (.leaf (130452503300000:ℤ)) (.branch 1279 (.leaf (5472650700000:ℤ)) (.leaf (8834626600000:ℤ)))) (.branch 2164 (.leaf (5558136400000:ℤ)) (.branch 2813 (.leaf (1752701400000:ℤ)) (.leaf (1704643700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 169 (.branch 140 (.leaf (1821498416303695:ℤ)) (.branch 152 (.leaf (2109085224570140:ℤ)) (.leaf (2260080445929050:ℤ)))) (.branch 188 (.leaf (2497004810598228:ℤ)) (.branch 200 (.leaf (2798521761296223:ℤ)) (.leaf (3011979868856579:ℤ))))), (.branch 169 (.branch 140 (.leaf (1828264034347033:ℤ)) (.branch 152 (.leaf (2121314830389142:ℤ)) (.leaf (2275785936232257:ℤ)))) (.branch 188 (.leaf (2518978419082196:ℤ)) (.branch 200 (.leaf (2829861448411943:ℤ)) (.leaf (3050856373948876:ℤ))))), (.branch 169 (.branch 140 (.leaf (1823701583050451:ℤ)) (.branch 152 (.leaf (2113330653029455:ℤ)) (.leaf (2265699269056039:ℤ)))) (.branch 188 (.leaf (2505215067205106:ℤ)) (.branch 200 (.leaf (2810828090640474:ℤ)) (.leaf (3027743246608649:ℤ))))), (.branch 169 (.branch 140 (.leaf (1830751991097151:ℤ)) (.branch 152 (.leaf (2126119235833571:ℤ)) (.leaf (2282152026945050:ℤ)))) (.branch 188 (.leaf (2528298152183075:ℤ)) (.branch 200 (.leaf (2843864952831070:ℤ)) (.leaf (3068824935868893:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 12 8) 8000 (endpointMeanRuns 12 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 12 8, EndpointRunConditions (endpointMeanCutoff 12 8) (endpointMeanBox 12 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 12 8 h) (endpointMeanCornerA 12 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 8, endpointJoint24Q (endpointMeanCornerK 12 8 h) (endpointMeanCornerA 12 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 12 8, endpointRunWeightQ (endpointMeanCutoff 12 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 12 8) = (225855963/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 12 8 h = (logRoundedQ ((endpointMeanCutoff 12 8:ℚ)/200)).2+(225855963/500000000000000:ℚ)+((endpointMeanRuns 12 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 12 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 12 8) r*endpointJoint24Q (endpointMeanCornerK 12 8 h) (endpointMeanCornerA 12 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 12 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 12 8 h≤endpointMeanCorner 12 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 12 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint12_08

namespace EndpointAnalyticJoint12_09
private noncomputable def weights : IntegerLookupTree := (.branch 1631 (.branch 1279 (.branch 1125 (.leaf (126082981000000:ℤ)) (.leaf (5436035600000:ℤ))) (.branch 1481 (.leaf (5049157600000:ℤ)) (.leaf (2367914300000:ℤ)))) (.branch 2164 (.branch 1907 (.leaf (3001347300000:ℤ)) (.leaf (1454048800000:ℤ))) (.branch 2813 (.leaf (1744012100000:ℤ)) (.leaf (1697008900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 169 (.branch 152 (.branch 140 (.leaf (1828264034347033:ℤ)) (.leaf (2121314830389142:ℤ))) (.branch 159 (.leaf (2275785936232257:ℤ)) (.leaf (2372268123926583:ℤ)))) (.branch 188 (.branch 176 (.leaf (2518978419082196:ℤ)) (.leaf (2628357567193494:ℤ))) (.branch 200 (.leaf (2829861448411943:ℤ)) (.leaf (3050856373948876:ℤ))))), (.branch 169 (.branch 152 (.branch 140 (.leaf (1835054782023809:ℤ)) (.leaf (2133615350013212:ℤ))) (.branch 159 (.leaf (2291600565316836:ℤ)) (.leaf (2390484641459213:ℤ)))) (.branch 188 (.branch 176 (.leaf (2541145395022953:ℤ)) (.leaf (2653699258753743:ℤ))) (.branch 200 (.leaf (2861552097954368:ℤ)) (.leaf (3090234669462753:ℤ))))), (.branch 169 (.branch 152 (.branch 140 (.leaf (1830751991097151:ℤ)) (.leaf (2126119235833571:ℤ))) (.branch 159 (.leaf (2282152026945050:ℤ)) (.leaf (2379732717053012:ℤ)))) (.branch 188 (.branch 176 (.leaf (2528298152183075:ℤ)) (.leaf (2639207539851630:ℤ))) (.branch 200 (.leaf (2843864952831070:ℤ)) (.leaf (3068824935868893:ℤ))))), (.branch 169 (.branch 152 (.branch 140 (.leaf (1837829655935245:ℤ)) (.leaf (2138985207308454:ℤ))) (.branch 159 (.leaf (2298724259314122:ℤ)) (.leaf (2398843782595127:ℤ)))) (.branch 188 (.branch 176 (.leaf (2551593925013307:ℤ)) (.leaf (2665873807039625:ℤ))) (.branch 200 (.leaf (2877290111362898:ℤ)) (.leaf (3110464038705857:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 12 9) 8000 (endpointMeanRuns 12 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 12 9, EndpointRunConditions (endpointMeanCutoff 12 9) (endpointMeanBox 12 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 12 9 h) (endpointMeanCornerA 12 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 9, endpointJoint24Q (endpointMeanCornerK 12 9 h) (endpointMeanCornerA 12 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 12 9, endpointRunWeightQ (endpointMeanCutoff 12 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 12 9) = (112549303/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 12 9 h = (logRoundedQ ((endpointMeanCutoff 12 9:ℚ)/200)).2+(112549303/250000000000000:ℚ)+((endpointMeanRuns 12 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 12 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 12 9) r*endpointJoint24Q (endpointMeanCornerK 12 9 h) (endpointMeanCornerA 12 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 12 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 12 9 h≤endpointMeanCorner 12 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 12 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint12_09

namespace EndpointAnalyticJoint12_10
private noncomputable def weights : IntegerLookupTree := (.branch 1631 (.branch 1279 (.branch 1125 (.leaf (122554265200000:ℤ)) (.leaf (5405886800000:ℤ))) (.branch 1481 (.leaf (5022963600000:ℤ)) (.leaf (2356330600000:ℤ)))) (.branch 2164 (.branch 1907 (.leaf (2987412100000:ℤ)) (.leaf (1447691800000:ℤ))) (.branch 2813 (.leaf (1736857400000:ℤ)) (.leaf (1690722400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 169 (.branch 152 (.branch 140 (.leaf (1835054782023809:ℤ)) (.leaf (2133615350013212:ℤ))) (.branch 159 (.leaf (2291600565316836:ℤ)) (.leaf (2390484641459213:ℤ)))) (.branch 188 (.branch 176 (.leaf (2541145395022953:ℤ)) (.leaf (2653699258753743:ℤ))) (.branch 200 (.leaf (2861552097954368:ℤ)) (.leaf (3090234669462753:ℤ))))), (.branch 169 (.branch 152 (.branch 140 (.leaf (1841870752673384:ℤ)) (.leaf (2145987194638574:ℤ))) (.branch 159 (.leaf (2307525091597411:ℤ)) (.leaf (2408841042636384:ℤ)))) (.branch 188 (.branch 176 (.leaf (2563507440051493:ℤ)) (.leaf (2679285285917009:ℤ))) (.branch 200 (.leaf (2893597640231549:ℤ)) (.leaf (3130121232153945:ℤ))))), (.branch 169 (.branch 152 (.branch 140 (.leaf (1837829655935245:ℤ)) (.leaf (2138985207308454:ℤ))) (.branch 159 (.leaf (2298724259314122:ℤ)) (.leaf (2398843782595127:ℤ)))) (.branch 188 (.branch 176 (.leaf (2551593925013307:ℤ)) (.leaf (2665873807039625:ℤ))) (.branch 200 (.leaf (2877290111362898:ℤ)) (.leaf (3110464038705857:ℤ))))), (.branch 169 (.branch 152 (.branch 140 (.leaf (1844934682939162:ℤ)) (.leaf (2151929035762954:ℤ))) (.branch 159 (.leaf (2315416833747380:ℤ)) (.leaf (2418108324543871:ℤ)))) (.branch 188 (.branch 176 (.leaf (2575104345404508:ℤ)) (.leaf (2692809507303650:ℤ))) (.branch 200 (.leaf (2911108130048566:ℤ)) (.leaf (3152668118340554:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 12 10) 8000 (endpointMeanRuns 12 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 12 10, EndpointRunConditions (endpointMeanCutoff 12 10) (endpointMeanBox 12 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 12 10 h) (endpointMeanCornerA 12 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 10, endpointJoint24Q (endpointMeanCornerK 12 10 h) (endpointMeanCornerA 12 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 12 10, endpointRunWeightQ (endpointMeanCutoff 12 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 12 10) = (448949999/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 12 10 h = (logRoundedQ ((endpointMeanCutoff 12 10:ℚ)/200)).2+(448949999/1000000000000000:ℚ)+((endpointMeanRuns 12 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 12 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 12 10) r*endpointJoint24Q (endpointMeanCornerK 12 10 h) (endpointMeanCornerA 12 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 12 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 12 10 h≤endpointMeanCorner 12 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 12 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint12_10

namespace EndpointAnalyticJoint12_11
private noncomputable def weights : IntegerLookupTree := (.branch 1631 (.branch 1279 (.branch 1125 (.leaf (119124590200000:ℤ)) (.leaf (5376061100000:ℤ))) (.branch 1356 (.leaf (1903327900000:ℤ)) (.branch 1481 (.leaf (2601467200000:ℤ)) (.leaf (2344871100000:ℤ))))) (.branch 2164 (.branch 1907 (.leaf (2973626200000:ℤ)) (.leaf (1441402900000:ℤ))) (.branch 2813 (.leaf (1729779300000:ℤ)) (.branch 3516 (.leaf (365469400000:ℤ)) (.leaf (243017600000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 169 (.branch 140 (.branch 132 (.leaf (1841870752673384:ℤ)) (.leaf (2046130874210011:ℤ))) (.branch 152 (.leaf (2145987194638574:ℤ)) (.branch 159 (.leaf (2307525091597411:ℤ)) (.leaf (2408841042636384:ℤ))))) (.branch 183 (.branch 176 (.leaf (2563507440051493:ℤ)) (.leaf (2679285285917009:ℤ))) (.branch 188 (.leaf (2801754940202042:ℤ)) (.branch 200 (.leaf (2893597640231549:ℤ)) (.leaf (3130121232153945:ℤ)))))), (.branch 169 (.branch 140 (.branch 132 (.leaf (1848712039981814:ℤ)) (.leaf (2056564870680922:ℤ))) (.branch 152 (.leaf (2158430777845796:ℤ)) (.branch 159 (.leaf (2323560278758899:ℤ)) (.leaf (2427338401616982:ℤ))))) (.branch 183 (.branch 176 (.leaf (2586066270773146:ℤ)) (.leaf (2705118004480537:ℤ))) (.branch 188 (.leaf (2831262974801709:ℤ)) (.branch 200 (.leaf (2926002049565725:ℤ)) (.leaf (3170522622375566:ℤ)))))), (.branch 169 (.branch 140 (.branch 132 (.leaf (1844934682939162:ℤ)) (.leaf (2051014901519133:ℤ))) (.branch 152 (.leaf (2151929035762954:ℤ)) (.branch 159 (.leaf (2315416833747380:ℤ)) (.leaf (2418108324543871:ℤ))))) (.branch 183 (.branch 176 (.leaf (2575104345404508:ℤ)) (.leaf (2692809507303650:ℤ))) (.branch 188 (.leaf (2817490271228899:ℤ)) (.branch 200 (.leaf (2911108130048566:ℤ)) (.leaf (3152668118340554:ℤ)))))), (.branch 169 (.branch 140 (.branch 132 (.leaf (1852067177890702:ℤ)) (.leaf (2061920650724021:ℤ))) (.branch 152 (.leaf (2164951192339815:ℤ)) (.branch 159 (.leaf (2332230624129037:ℤ)) (.leaf (2437527575431643:ℤ))))) (.branch 183 (.branch 176 (.leaf (2598831391122155:ℤ)) (.leaf (2720017362966324:ℤ))) (.branch 188 (.leaf (2848614001330272:ℤ)) (.branch 200 (.leaf (2945323626341136:ℤ)) (.leaf (3195444840614946:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 12 11) 8000 (endpointMeanRuns 12 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 12 11, EndpointRunConditions (endpointMeanCutoff 12 11) (endpointMeanBox 12 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 12 11 h) (endpointMeanCornerA 12 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 11, endpointJoint24Q (endpointMeanCornerK 12 11 h) (endpointMeanCornerA 12 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 12 11, endpointRunWeightQ (endpointMeanCutoff 12 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 12 11) = (223858077/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 12 11 h = (logRoundedQ ((endpointMeanCutoff 12 11:ℚ)/200)).2+(223858077/500000000000000:ℚ)+((endpointMeanRuns 12 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 12 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 12 11) r*endpointJoint24Q (endpointMeanCornerK 12 11 h) (endpointMeanCornerA 12 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 12 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 12 11 h≤endpointMeanCorner 12 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 12 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint12_11

namespace EndpointAnalyticJoint12_12
private noncomputable def weights : IntegerLookupTree := (.branch 1481 (.branch 1237 (.branch 1125 (.leaf (115135545200000:ℤ)) (.branch 1185 (.leaf (2046709700000:ℤ)) (.leaf (1560744300000:ℤ)))) (.branch 1356 (.branch 1279 (.leaf (1127717800000:ℤ)) (.leaf (1891410800000:ℤ))) (.branch 1407 (.leaf (1058547900000:ℤ)) (.leaf (1370610200000:ℤ))))) (.branch 2164 (.branch 1786 (.branch 1631 (.leaf (2331279800000:ℤ)) (.leaf (1704167000000:ℤ))) (.branch 1907 (.leaf (937322500000:ℤ)) (.leaf (1433944100000:ℤ)))) (.branch 2813 (.branch 2344 (.leaf (560795500000:ℤ)) (.leaf (842974300000:ℤ))) (.branch 3516 (.leaf (363848800000:ℤ)) (.leaf (242022900000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 169 (.branch 148 (.branch 132 (.leaf (1848712039981814:ℤ)) (.branch 140 (.leaf (2056564870680922:ℤ)) (.leaf (2158430777845796:ℤ)))) (.branch 159 (.branch 152 (.leaf (2266787551305497:ℤ)) (.leaf (2323560278758899:ℤ))) (.branch 163 (.leaf (2427338401616982:ℤ)) (.leaf (2489296687095360:ℤ))))) (.branch 188 (.branch 180 (.branch 176 (.leaf (2586066270773146:ℤ)) (.leaf (2705118004480537:ℤ))) (.branch 183 (.leaf (2776299234498777:ℤ)) (.leaf (2831262974801709:ℤ)))) (.branch 195 (.branch 191 (.leaf (2926002049565725:ℤ)) (.leaf (2984798684739503:ℤ))) (.branch 200 (.leaf (3065570991632833:ℤ)) (.leaf (3170522622375566:ℤ)))))), (.branch 169 (.branch 148 (.branch 132 (.leaf (1855578737983134:ℤ)) (.branch 140 (.leaf (2067052074052584:ℤ)) (.leaf (2170946515613596:ℤ)))) (.branch 159 (.branch 152 (.leaf (2281638802987481:ℤ)) (.leaf (2339706895793127:ℤ))) (.branch 163 (.leaf (2445977800808286:ℤ)) (.leaf (2509500092308954:ℤ))))) (.branch 188 (.branch 180 (.branch 176 (.leaf (2608823618899341:ℤ)) (.leaf (2731199792955316:ℤ))) (.branch 183 (.leaf (2804462969990779:ℤ)) (.leaf (2861081787511709:ℤ)))) (.branch 195 (.branch 191 (.leaf (2958769344786214:ℤ)) (.leaf (3019455933825352:ℤ))) (.branch 200 (.leaf (3102898475408352:ℤ)) (.leaf (3211445485157119:ℤ)))))), (.branch 169 (.branch 148 (.branch 132 (.leaf (1852067177890702:ℤ)) (.branch 140 (.leaf (2061920650724021:ℤ)) (.leaf (2164951192339815:ℤ)))) (.branch 159 (.branch 152 (.leaf (2274681934042779:ℤ)) (.leaf (2332230624129037:ℤ))) (.branch 163 (.leaf (2437527575431643:ℤ)) (.leaf (2500454846018270:ℤ))))) (.branch 188 (.branch 180 (.branch 176 (.leaf (2598831391122155:ℤ)) (.leaf (2720017362966324:ℤ))) (.branch 183 (.leaf (2792557896026119:ℤ)) (.leaf (2848614001330272:ℤ)))) (.branch 195 (.branch 191 (.leaf (2945323626341136:ℤ)) (.leaf (3005399140249653:ℤ))) (.branch 200 (.leaf (3087998291876361:ℤ)) (.leaf (3195444840614946:ℤ)))))), (.branch 169 (.branch 148 (.branch 132 (.leaf (1859227246980616:ℤ)) (.branch 140 (.leaf (2072884388471864:ℤ)) (.leaf (2178052151032871:ℤ)))) (.branch 159 (.branch 152 (.leaf (2290248330305162:ℤ)) (.leaf (2349166510689179:ℤ))) (.branch 163 (.leaf (2457102777689008:ℤ)) (.leaf (2521688478265302:ℤ))))) (.branch 188 (.branch 180 (.branch 176 (.leaf (2622777058154889:ℤ)) (.leaf (2747500123856334:ℤ))) (.branch 183 (.leaf (2822259531626377:ℤ)) (.leaf (2880081543293330:ℤ)))) (.branch 195 (.branch 191 (.leaf (2979941271964560:ℤ)) (.leaf (3042038702848354:ℤ))) (.branch 200 (.leaf (3127498036678281:ℤ)) (.leaf (3238801975384359:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 12 12) 8000 (endpointMeanRuns 12 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 12 12, EndpointRunConditions (endpointMeanCutoff 12 12) (endpointMeanBox 12 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 12 12 h) (endpointMeanCornerA 12 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 12, endpointJoint24Q (endpointMeanCornerK 12 12 h) (endpointMeanCornerA 12 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 12 12, endpointRunWeightQ (endpointMeanCutoff 12 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 12 12) = (111563197/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 12 12 h = (logRoundedQ ((endpointMeanCutoff 12 12:ℚ)/200)).2+(111563197/250000000000000:ℚ)+((endpointMeanRuns 12 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 12 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 12 12) r*endpointJoint24Q (endpointMeanCornerK 12 12 h) (endpointMeanCornerA 12 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 12 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 12 12 h≤endpointMeanCorner 12 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 12 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint12_12

namespace EndpointAnalyticJoint12_13
private noncomputable def weights : IntegerLookupTree := (.branch 1631 (.branch 1279 (.branch 1185 (.branch 1125 (.leaf (111913459600000:ℤ)) (.leaf (2035348200000:ℤ))) (.branch 1237 (.leaf (1552294500000:ℤ)) (.leaf (1121731500000:ℤ)))) (.branch 1407 (.branch 1356 (.leaf (1881594400000:ℤ)) (.leaf (1053183200000:ℤ))) (.branch 1481 (.leaf (1363807300000:ℤ)) (.branch 1563 (.leaf (1280521900000:ℤ)) (.leaf (885076300000:ℤ)))))) (.branch 2164 (.branch 1786 (.branch 1705 (.leaf (824933400000:ℤ)) (.leaf (761653900000:ℤ))) (.branch 1907 (.leaf (933153700000:ℤ)) (.branch 2009 (.leaf (597885500000:ℤ)) (.leaf (700905900000:ℤ))))) (.branch 2813 (.branch 2344 (.leaf (558494500000:ℤ)) (.leaf (839663200000:ℤ))) (.branch 3516 (.leaf (362513900000:ℤ)) (.branch 4687 (.leaf (89254200000:ℤ)) (.leaf (9335200000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 148 (.branch 132 (.branch 124 (.leaf (1855578737983134:ℤ)) (.leaf (1969446166805350:ℤ))) (.branch 140 (.leaf (2067052074052584:ℤ)) (.leaf (2170946515613596:ℤ)))) (.branch 156 (.branch 152 (.leaf (2281638802987481:ℤ)) (.leaf (2339706895793127:ℤ))) (.branch 159 (.leaf (2399688545923277:ℤ)) (.branch 163 (.leaf (2445977800808286:ℤ)) (.leaf (2509500092308954:ℤ)))))) (.branch 183 (.branch 172 (.branch 169 (.leaf (2558541191961598:ℤ)) (.leaf (2608823618899341:ℤ))) (.branch 176 (.leaf (2660386593936277:ℤ)) (.branch 180 (.leaf (2731199792955316:ℤ)) (.leaf (2804462969990779:ℤ))))) (.branch 191 (.branch 188 (.leaf (2861081787511709:ℤ)) (.leaf (2958769344786214:ℤ))) (.branch 195 (.leaf (3019455933825352:ℤ)) (.branch 200 (.leaf (3102898475408352:ℤ)) (.leaf (3211445485157119:ℤ))))))), (.branch 166 (.branch 148 (.branch 132 (.branch 124 (.leaf (1862470941060643:ℤ)) (.leaf (1978214874676821:ℤ))) (.branch 140 (.leaf (2077592755647146:ℤ)) (.leaf (2183534826332761:ℤ)))) (.branch 156 (.branch 152 (.leaf (2296587355219926:ℤ)) (.leaf (2355965717035716:ℤ))) (.branch 159 (.leaf (2417351990512684:ℤ)) (.branch 163 (.leaf (2464760330929327:ℤ)) (.leaf (2529867470577402:ℤ)))))) (.branch 183 (.branch 172 (.branch 169 (.leaf (2580170544101329:ℤ)) (.leaf (2631781231380546:ℤ))) (.branch 176 (.leaf (2684742007173314:ℤ)) (.branch 180 (.leaf (2757533052785103:ℤ)) (.leaf (2832912408114187:ℤ))))) (.branch 191 (.branch 188 (.leaf (2891214651441729:ℤ)) (.leaf (2991903589727813:ℤ))) (.branch 195 (.leaf (3054515596956858:ℤ)) (.branch 200 (.leaf (3140680471915372:ℤ)) (.leaf (3252896551297456:ℤ))))))), (.branch 166 (.branch 148 (.branch 132 (.branch 124 (.leaf (1859227246980616:ℤ)) (.leaf (1974203045288379:ℤ))) (.branch 140 (.leaf (2072884388471864:ℤ)) (.leaf (2178052151032871:ℤ)))) (.branch 156 (.branch 152 (.leaf (2290248330305162:ℤ)) (.leaf (2349166510689179:ℤ))) (.branch 159 (.leaf (2410070664982070:ℤ)) (.branch 163 (.leaf (2457102777689008:ℤ)) (.leaf (2521688478265302:ℤ)))))) (.branch 183 (.branch 172 (.branch 169 (.leaf (2571585455269369:ℤ)) (.leaf (2622777058154889:ℤ))) (.branch 176 (.leaf (2675305683973737:ℤ)) (.branch 180 (.leaf (2747500123856334:ℤ)) (.leaf (2822259531626377:ℤ))))) (.branch 191 (.branch 188 (.leaf (2880081543293330:ℤ)) (.leaf (2979941271964560:ℤ))) (.branch 195 (.leaf (3042038702848354:ℤ)) (.branch 200 (.leaf (3127498036678281:ℤ)) (.leaf (3238801975384359:ℤ))))))), (.branch 166 (.branch 148 (.branch 132 (.branch 124 (.leaf (1866414996810180:ℤ)) (.leaf (1983360953127502:ℤ))) (.branch 140 (.leaf (2083906423101966:ℤ)) (.leaf (2191232388704260:ℤ)))) (.branch 156 (.branch 152 (.leaf (2305921252534531:ℤ)) (.leaf (2366225380049827:ℤ))) (.branch 159 (.leaf (2428616904179621:ℤ)) (.branch 163 (.leaf (2476835183724205:ℤ)) (.leaf (2543102424561645:ℤ)))))) (.branch 183 (.branch 172 (.branch 169 (.leaf (2594339741754428:ℤ)) (.leaf (2646943360882427:ℤ))) (.branch 176 (.leaf (2700959298790092:ℤ)) (.branch 180 (.leaf (2775260567586317:ℤ)) (.leaf (2852277073714582:ℤ))))) (.branch 191 (.branch 188 (.leaf (2911896695075313:ℤ)) (.leaf (3014965793551560:ℤ))) (.branch 195 (.leaf (3079124947396692:ℤ)) (.branch 200 (.leaf (3167503037536694:ℤ)) (.leaf (3282747397928773:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 12 13) 8000 (endpointMeanRuns 12 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 12 13, EndpointRunConditions (endpointMeanCutoff 12 13) (endpointMeanBox 12 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 12 13 h) (endpointMeanCornerA 12 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 13, endpointJoint24Q (endpointMeanCornerK 12 13 h) (endpointMeanCornerA 12 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 12 13, endpointRunWeightQ (endpointMeanCutoff 12 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 12 13) = (445047367/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 12 13 h = (logRoundedQ ((endpointMeanCutoff 12 13:ℚ)/200)).2+(445047367/1000000000000000:ℚ)+((endpointMeanRuns 12 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 12 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 12 13) r*endpointJoint24Q (endpointMeanCornerK 12 13 h) (endpointMeanCornerA 12 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 12 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 12 13 h≤endpointMeanCorner 12 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 12 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint12_13

namespace EndpointAnalyticJoint12_14
private noncomputable def weights : IntegerLookupTree := (.branch 1631 (.branch 1279 (.branch 1185 (.branch 1125 (.leaf (108781268000000:ℤ)) (.leaf (2024104400000:ℤ))) (.branch 1237 (.leaf (1543932300000:ℤ)) (.leaf (1115807300000:ℤ)))) (.branch 1407 (.branch 1356 (.leaf (1871879700000:ℤ)) (.leaf (1047874100000:ℤ))) (.branch 1481 (.leaf (1357074800000:ℤ)) (.branch 1563 (.leaf (1274354700000:ℤ)) (.leaf (880908000000:ℤ)))))) (.branch 2164 (.branch 1786 (.branch 1705 (.leaf (821123500000:ℤ)) (.leaf (758205900000:ℤ))) (.branch 1907 (.leaf (929028100000:ℤ)) (.branch 2009 (.leaf (595307700000:ℤ)) (.leaf (697959500000:ℤ))))) (.branch 2813 (.branch 2344 (.leaf (556217400000:ℤ)) (.leaf (836386400000:ℤ))) (.branch 3516 (.leaf (361192800000:ℤ)) (.branch 4687 (.leaf (88952700000:ℤ)) (.leaf (9306300000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 148 (.branch 132 (.branch 124 (.leaf (1862470941060643:ℤ)) (.leaf (1978214874676821:ℤ))) (.branch 140 (.leaf (2077592755647146:ℤ)) (.leaf (2183534826332761:ℤ)))) (.branch 156 (.branch 152 (.leaf (2296587355219926:ℤ)) (.leaf (2355965717035716:ℤ))) (.branch 159 (.leaf (2417351990512684:ℤ)) (.branch 163 (.leaf (2464760330929327:ℤ)) (.leaf (2529867470577402:ℤ)))))) (.branch 183 (.branch 172 (.branch 169 (.leaf (2580170544101329:ℤ)) (.leaf (2631781231380546:ℤ))) (.branch 176 (.leaf (2684742007173314:ℤ)) (.branch 180 (.leaf (2757533052785103:ℤ)) (.leaf (2832912408114187:ℤ))))) (.branch 191 (.branch 188 (.leaf (2891214651441729:ℤ)) (.leaf (2991903589727813:ℤ))) (.branch 195 (.leaf (3054515596956858:ℤ)) (.branch 200 (.leaf (3140680471915372:ℤ)) (.leaf (3252896551297456:ℤ))))))), (.branch 166 (.branch 148 (.branch 132 (.branch 124 (.leaf (1869388743948226:ℤ)) (.leaf (1987022624101712:ℤ))) (.branch 140 (.leaf (2088187188170321:ℤ)) (.leaf (2196196130820140:ℤ)))) (.branch 156 (.branch 152 (.leaf (2311633845484262:ℤ)) (.leaf (2372337522203204:ℤ))) (.branch 159 (.leaf (2435145450839045:ℤ)) (.branch 163 (.leaf (2483687091074705:ℤ)) (.leaf (2550400152724022:ℤ)))))) (.branch 183 (.branch 172 (.branch 169 (.leaf (2601982746091379:ℤ)) (.leaf (2654940870540378:ℤ))) (.branch 176 (.leaf (2709320390318289:ℤ)) (.branch 180 (.leaf (2784120208567520:ℤ)) (.leaf (2861650447134880:ℤ))))) (.branch 191 (.branch 188 (.leaf (2921664874173789:ℤ)) (.leaf (3025408893734827:ℤ))) (.branch 195 (.leaf (3089982346664829:ℤ)) (.branch 200 (.leaf (3178922515462724:ℤ)) (.leaf (3294882638471815:ℤ))))))), (.branch 166 (.branch 148 (.branch 132 (.branch 124 (.leaf (1866414996810180:ℤ)) (.leaf (1983360953127502:ℤ))) (.branch 140 (.leaf (2083906423101966:ℤ)) (.leaf (2191232388704260:ℤ)))) (.branch 156 (.branch 152 (.leaf (2305921252534531:ℤ)) (.leaf (2366225380049827:ℤ))) (.branch 159 (.leaf (2428616904179621:ℤ)) (.branch 163 (.leaf (2476835183724205:ℤ)) (.leaf (2543102424561645:ℤ)))))) (.branch 183 (.branch 172 (.branch 169 (.leaf (2594339741754428:ℤ)) (.leaf (2646943360882427:ℤ))) (.branch 176 (.leaf (2700959298790092:ℤ)) (.branch 180 (.leaf (2775260567586317:ℤ)) (.leaf (2852277073714582:ℤ))))) (.branch 191 (.branch 188 (.leaf (2911896695075313:ℤ)) (.leaf (3014965793551560:ℤ))) (.branch 195 (.leaf (3079124947396692:ℤ)) (.branch 200 (.leaf (3167503037536694:ℤ)) (.leaf (3282747397928773:ℤ))))))), (.branch 166 (.branch 148 (.branch 132 (.branch 124 (.leaf (1873630534392801:ℤ)) (.leaf (1992561342552395:ℤ))) (.branch 140 (.leaf (2094987064593148:ℤ)) (.leaf (2204492385101814:ℤ)))) (.branch 156 (.branch 152 (.leaf (2321701429723088:ℤ)) (.leaf (2383408125271354:ℤ))) (.branch 159 (.leaf (2447305862424110:ℤ)) (.branch 163 (.leaf (2496726056003249:ℤ)) (.leaf (2564698216117597:ℤ)))))) (.branch 183 (.branch 172 (.branch 169 (.leaf (2617295366115462:ℤ)) (.leaf (2671332332244987:ℤ))) (.branch 176 (.leaf (2726858907160421:ℤ)) (.branch 180 (.leaf (2803301499833623:ℤ)) (.leaf (2882613882270996:ℤ))))) (.branch 191 (.branch 188 (.leaf (2944063296588042:ℤ)) (.leaf (3050401973288987:ℤ))) (.branch 195 (.leaf (3116663319504553:ℤ)) (.branch 200 (.leaf (3208019757371400:ℤ)) (.leaf (3327289090383257:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 12 14) 8000 (endpointMeanRuns 12 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 12 14, EndpointRunConditions (endpointMeanCutoff 12 14) (endpointMeanBox 12 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 12 14 h) (endpointMeanCornerA 12 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 14, endpointJoint24Q (endpointMeanCornerK 12 14 h) (endpointMeanCornerA 12 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 12 14, endpointRunWeightQ (endpointMeanCutoff 12 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 12 14) = (221927219/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 12 14 h = (logRoundedQ ((endpointMeanCutoff 12 14:ℚ)/200)).2+(221927219/500000000000000:ℚ)+((endpointMeanRuns 12 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 12 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 12 14) r*endpointJoint24Q (endpointMeanCornerK 12 14 h) (endpointMeanCornerA 12 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 12 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 12 14 h≤endpointMeanCorner 12 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 12 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint12_14

namespace EndpointAnalyticJoint12_15
private noncomputable def weights : IntegerLookupTree := (.branch 1563 (.branch 1279 (.branch 1185 (.branch 1125 (.leaf (105137556800000:ℤ)) (.leaf (2010763900000:ℤ))) (.branch 1237 (.leaf (1534010800000:ℤ)) (.leaf (1108778300000:ℤ)))) (.branch 1407 (.branch 1356 (.leaf (1860353300000:ℤ)) (.leaf (1041574900000:ℤ))) (.branch 1481 (.leaf (1349086900000:ℤ)) (.leaf (1267037400000:ℤ))))) (.branch 2164 (.branch 1786 (.branch 1631 (.leaf (875962400000:ℤ)) (.leaf (1679343600000:ℤ))) (.branch 1907 (.leaf (924133200000:ℤ)) (.leaf (1414505500000:ℤ)))) (.branch 2813 (.branch 2344 (.leaf (553515600000:ℤ)) (.leaf (832498600000:ℤ))) (.branch 3516 (.leaf (359625300000:ℤ)) (.leaf (239430500000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 172 (.branch 152 (.branch 140 (.branch 132 (.leaf (1869388743948226:ℤ)) (.leaf (2088187188170321:ℤ))) (.branch 148 (.leaf (2196196130820140:ℤ)) (.leaf (2311633845484262:ℤ)))) (.branch 163 (.branch 159 (.leaf (2372337522203204:ℤ)) (.leaf (2483687091074705:ℤ))) (.branch 169 (.leaf (2550400152724022:ℤ)) (.leaf (2654940870540378:ℤ))))) (.branch 188 (.branch 180 (.branch 176 (.leaf (2709320390318289:ℤ)) (.leaf (2784120208567520:ℤ))) (.branch 183 (.leaf (2861650447134880:ℤ)) (.leaf (2921664874173789:ℤ)))) (.branch 195 (.branch 191 (.leaf (3025408893734827:ℤ)) (.leaf (3089982346664829:ℤ))) (.branch 200 (.leaf (3178922515462724:ℤ)) (.leaf (3294882638471815:ℤ)))))), (.branch 172 (.branch 152 (.branch 140 (.branch 132 (.leaf (1876332241731625:ℤ)) (.leaf (2098835645718463:ℤ))) (.branch 148 (.leaf (2208930852332696:ℤ)) (.leaf (2326778915438484:ℤ)))) (.branch 163 (.branch 159 (.leaf (2388823096430446:ℤ)) (.leaf (2502759188778921:ℤ))) (.branch 169 (.leaf (2571099480373237:ℤ)) (.leaf (2678304314210865:ℤ))))) (.branch 188 (.branch 180 (.branch 176 (.leaf (2734123784625015:ℤ)) (.leaf (2810963708277306:ℤ))) (.branch 183 (.leaf (2890680014719738:ℤ)) (.leaf (2952435798125305:ℤ)))) (.branch 195 (.branch 191 (.leaf (3059289412170698:ℤ)) (.leaf (3125860909734015:ℤ))) (.branch 200 (.leaf (3217630207746955:ℤ)) (.leaf (3337410652353160:ℤ)))))), (.branch 172 (.branch 152 (.branch 140 (.branch 132 (.leaf (1873630534392801:ℤ)) (.leaf (2094987064593148:ℤ))) (.branch 148 (.leaf (2204492385101814:ℤ)) (.leaf (2321701429723088:ℤ)))) (.branch 163 (.branch 159 (.leaf (2383408125271354:ℤ)) (.leaf (2496726056003249:ℤ))) (.branch 169 (.leaf (2564698216117597:ℤ)) (.leaf (2671332332244987:ℤ))))) (.branch 188 (.branch 180 (.branch 176 (.leaf (2726858907160421:ℤ)) (.leaf (2803301499833623:ℤ))) (.branch 183 (.leaf (2882613882270996:ℤ)) (.leaf (2944063296588042:ℤ)))) (.branch 195 (.branch 191 (.leaf (3050401973288987:ℤ)) (.leaf (3116663319504553:ℤ))) (.branch 200 (.leaf (3208019757371400:ℤ)) (.leaf (3327289090383257:ℤ)))))), (.branch 172 (.branch 152 (.branch 140 (.branch 132 (.leaf (1880873967155590:ℤ)) (.leaf (2106126624572463:ℤ))) (.branch 148 (.leaf (2217832622876482:ℤ)) (.leaf (2337589595851783:ℤ)))) (.branch 163 (.branch 159 (.leaf (2400715645899247:ℤ)) (.leaf (2516776667130733:ℤ))) (.branch 169 (.leaf (2586477397146354:ℤ)) (.leaf (2695946023914342:ℤ))))) (.branch 188 (.branch 180 (.branch 176 (.leaf (2753006867926889:ℤ)) (.leaf (2831625754623859:ℤ))) (.branch 183 (.leaf (2913273353012601:ℤ)) (.leaf (2976585230161358:ℤ)))) (.branch 195 (.branch 191 (.leaf (3086254649570774:ℤ)) (.leaf (3154659331170603:ℤ))) (.branch 200 (.leaf (3249054741771822:ℤ)) (.leaf (3372435143187849:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 12 15) 8000 (endpointMeanRuns 12 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 12 15, EndpointRunConditions (endpointMeanCutoff 12 15) (endpointMeanBox 12 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 12 15 h) (endpointMeanCornerA 12 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 15, endpointJoint24Q (endpointMeanCornerK 12 15 h) (endpointMeanCornerA 12 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 12 15, endpointRunWeightQ (endpointMeanCutoff 12 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 12 15) = (442439053/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 12 15 h = (logRoundedQ ((endpointMeanCutoff 12 15:ℚ)/200)).2+(442439053/1000000000000000:ℚ)+((endpointMeanRuns 12 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 12 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 12 15) r*endpointJoint24Q (endpointMeanCornerK 12 15 h) (endpointMeanCornerA 12 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 12 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 12 15 h≤endpointMeanCorner 12 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 12 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint12_15

namespace EndpointAnalyticJoint12_16
private noncomputable def weights : IntegerLookupTree := (.branch 1481 (.branch 1185 (.branch 1125 (.leaf (102193886300000:ℤ)) (.leaf (1999770700000:ℤ))) (.branch 1279 (.leaf (2773612000000:ℤ)) (.branch 1356 (.leaf (1850855200000:ℤ)) (.leaf (2532184500000:ℤ))))) (.branch 2164 (.branch 1631 (.leaf (2285026600000:ℤ)) (.branch 1907 (.leaf (2901633300000:ℤ)) (.leaf (1408560700000:ℤ)))) (.branch 2813 (.leaf (1692815900000:ℤ)) (.branch 3516 (.leaf (358333700000:ℤ)) (.leaf (238637600000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 169 (.branch 140 (.branch 132 (.leaf (1876332241731625:ℤ)) (.leaf (2098835645718463:ℤ))) (.branch 152 (.leaf (2208930852332696:ℤ)) (.branch 159 (.leaf (2388823096430446:ℤ)) (.leaf (2502759188778921:ℤ))))) (.branch 188 (.branch 176 (.leaf (2678304314210865:ℤ)) (.branch 183 (.leaf (2810963708277306:ℤ)) (.leaf (2952435798125305:ℤ)))) (.branch 195 (.leaf (3059289412170698:ℤ)) (.branch 200 (.leaf (3217630207746955:ℤ)) (.leaf (3337410652353160:ℤ)))))), (.branch 169 (.branch 140 (.branch 132 (.leaf (1883301529849766:ℤ)) (.leaf (2109538403785637:ℤ))) (.branch 152 (.leaf (2221739416581666:ℤ)) (.branch 159 (.leaf (2405423230308266:ℤ)) (.leaf (2521977740081151:ℤ))))) (.branch 188 (.branch 176 (.leaf (2701873355868936:ℤ)) (.branch 183 (.leaf (2838066023491698:ℤ)) (.leaf (2983530800915984:ℤ)))) (.branch 195 (.leaf (3093549346933348:ℤ)) (.branch 200 (.leaf (3256809218672849:ℤ)) (.leaf (3380487587747997:ℤ)))))), (.branch 169 (.branch 140 (.branch 132 (.leaf (1880873967155590:ℤ)) (.leaf (2106126624572463:ℤ))) (.branch 152 (.leaf (2217832622876482:ℤ)) (.branch 159 (.leaf (2400715645899247:ℤ)) (.leaf (2516776667130733:ℤ))))) (.branch 188 (.branch 176 (.leaf (2695946023914342:ℤ)) (.branch 183 (.leaf (2831625754623859:ℤ)) (.leaf (2976585230161358:ℤ)))) (.branch 195 (.leaf (3086254649570774:ℤ)) (.branch 200 (.leaf (3249054741771822:ℤ)) (.leaf (3372435143187849:ℤ)))))), (.branch 169 (.branch 140 (.branch 132 (.leaf (1888145402940972:ℤ)) (.leaf (2117325416323956:ℤ))) (.branch 152 (.leaf (2231253587599945:ℤ)) (.branch 159 (.leaf (2418148848011190:ℤ)) (.leaf (2536988299931230:ℤ))))) (.branch 188 (.branch 176 (.leaf (2720786506466391:ℤ)) (.branch 183 (.leaf (2860236194617317:ℤ)) (.leaf (3009466421011710:ℤ)))) (.branch 195 (.leaf (3122528717658567:ℤ)) (.branch 200 (.leaf (3290614620054485:ℤ)) (.leaf (3418193756557051:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 12 16) 8000 (endpointMeanRuns 12 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 12 16, EndpointRunConditions (endpointMeanCutoff 12 16) (endpointMeanBox 12 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 12 16 h) (endpointMeanCornerA 12 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 12 16, endpointJoint24Q (endpointMeanCornerK 12 16 h) (endpointMeanCornerA 12 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 12 16, endpointRunWeightQ (endpointMeanCutoff 12 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 12 16) = (220636357/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 12 16 h = (logRoundedQ ((endpointMeanCutoff 12 16:ℚ)/200)).2+(220636357/500000000000000:ℚ)+((endpointMeanRuns 12 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 12 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 12 16) r*endpointJoint24Q (endpointMeanCornerK 12 16 h) (endpointMeanCornerA 12 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 12 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 12 16 h≤endpointMeanCorner 12 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 12 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint12_16

namespace EndpointAnalyticJoint13_02
private noncomputable def weights : IntegerLookupTree := (.branch 1733 (.branch 1092 (.leaf (151683561300000:ℤ)) (.leaf (27997025100000:ℤ))) (.branch 2323 (.leaf (5201715300000:ℤ)) (.leaf (7100230400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 147 (.leaf (1778249579987330:ℤ)) (.leaf (2125193077577116:ℤ))) (.branch 200 (.leaf (2313452583477037:ℤ)) (.leaf (2823107618194363:ℤ)))), (.branch 163 (.branch 147 (.leaf (1779545524129293:ℤ)) (.leaf (2127942266822951:ℤ))) (.branch 200 (.leaf (2317219935404214:ℤ)) (.leaf (2830438303131011:ℤ)))), (.branch 163 (.branch 147 (.leaf (1779007859100967:ℤ)) (.leaf (2126954478081989:ℤ))) (.branch 200 (.leaf (2315975203611773:ℤ)) (.leaf (2828566235553695:ℤ)))), (.branch 163 (.branch 147 (.leaf (1780356375455862:ℤ)) (.leaf (2129826875998134:ℤ))) (.branch 200 (.leaf (2319919937730758:ℤ)) (.leaf (2836286568534853:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 13 2) 8000 (endpointMeanRuns 13 2) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 13 2, EndpointRunConditions (endpointMeanCutoff 13 2) (endpointMeanBox 13 2).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 2, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 13 2 h) (endpointMeanCornerA 13 2 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 2, endpointJoint24Q (endpointMeanCornerK 13 2 h) (endpointMeanCornerA 13 2 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 13 2, endpointRunWeightQ (endpointMeanCutoff 13 2) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 13 2) = (229528353/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 13 2 h = (logRoundedQ ((endpointMeanCutoff 13 2:ℚ)/200)).2+(229528353/500000000000000:ℚ)+((endpointMeanRuns 13 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 13 2).map (fun r => endpointRunWeightQ (endpointMeanCutoff 13 2) r*endpointJoint24Q (endpointMeanCornerK 13 2 h) (endpointMeanCornerA 13 2 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 13 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 13 2 h≤endpointMeanCorner 13 2 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 13 2 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint13_02

namespace EndpointAnalyticJoint13_03
private noncomputable def weights : IntegerLookupTree := (.branch 1733 (.branch 1092 (.leaf (149099605600000:ℤ)) (.leaf (27903236600000:ℤ))) (.branch 2323 (.leaf (5187132700000:ℤ)) (.leaf (7082597100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 147 (.leaf (1779545524129293:ℤ)) (.leaf (2127942266822951:ℤ))) (.branch 200 (.leaf (2317219935404214:ℤ)) (.leaf (2830438303131011:ℤ)))), (.branch 163 (.branch 147 (.leaf (1786295658286410:ℤ)) (.leaf (2142286938231662:ℤ))) (.branch 200 (.leaf (2336897553667233:ℤ)) (.leaf (2868842876230053:ℤ)))), (.branch 163 (.branch 147 (.leaf (1780356375455862:ℤ)) (.leaf (2129826875998134:ℤ))) (.branch 200 (.leaf (2319919937730758:ℤ)) (.leaf (2836286568534853:ℤ)))), (.branch 163 (.branch 147 (.leaf (1787380976733567:ℤ)) (.leaf (2144817062921890:ℤ))) (.branch 200 (.leaf (2340528832533225:ℤ)) (.leaf (2876749086179229:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 13 3) 8000 (endpointMeanRuns 13 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 13 3, EndpointRunConditions (endpointMeanCutoff 13 3) (endpointMeanBox 13 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 13 3 h) (endpointMeanCornerA 13 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 3, endpointJoint24Q (endpointMeanCornerK 13 3 h) (endpointMeanCornerA 13 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 13 3, endpointRunWeightQ (endpointMeanCutoff 13 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 13 3) = (458246973/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 13 3 h = (logRoundedQ ((endpointMeanCutoff 13 3:ℚ)/200)).2+(458246973/1000000000000000:ℚ)+((endpointMeanRuns 13 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 13 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 13 3) r*endpointJoint24Q (endpointMeanCornerK 13 3 h) (endpointMeanCornerA 13 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 13 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 13 3 h≤endpointMeanCorner 13 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 13 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint13_03

namespace EndpointAnalyticJoint13_04
private noncomputable def weights : IntegerLookupTree := (.branch 1733 (.branch 1092 (.leaf (144064394500000:ℤ)) (.leaf (27717615700000:ℤ))) (.branch 2323 (.leaf (5158271500000:ℤ)) (.leaf (7047698100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 147 (.leaf (1786295658286410:ℤ)) (.leaf (2142286938231662:ℤ))) (.branch 200 (.leaf (2336897553667233:ℤ)) (.leaf (2868842876230053:ℤ)))), (.branch 163 (.branch 147 (.leaf (1793071396908557:ℤ)) (.leaf (2156728308503424:ℤ))) (.branch 200 (.leaf (2356742272452128:ℤ)) (.leaf (2907768538671797:ℤ)))), (.branch 163 (.branch 147 (.leaf (1787380976733567:ℤ)) (.leaf (2144817062921890:ℤ))) (.branch 200 (.leaf (2340528832533225:ℤ)) (.leaf (2876749086179229:ℤ)))), (.branch 163 (.branch 147 (.leaf (1794433294385244:ℤ)) (.leaf (2159912754056600:ℤ))) (.branch 200 (.leaf (2361320805440270:ℤ)) (.leaf (2917788842862945:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 13 4) 8000 (endpointMeanRuns 13 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 13 4, EndpointRunConditions (endpointMeanCutoff 13 4) (endpointMeanBox 13 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 13 4 h) (endpointMeanCornerA 13 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 4, endpointJoint24Q (endpointMeanCornerK 13 4 h) (endpointMeanCornerA 13 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 13 4, endpointRunWeightQ (endpointMeanCutoff 13 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 13 4) = (91328879/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 13 4 h = (logRoundedQ ((endpointMeanCutoff 13 4:ℚ)/200)).2+(91328879/200000000000000:ℚ)+((endpointMeanRuns 13 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 13 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 13 4) r*endpointJoint24Q (endpointMeanCornerK 13 4 h) (endpointMeanCornerA 13 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 13 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 13 4 h≤endpointMeanCorner 13 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 13 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint13_04

namespace EndpointAnalyticJoint13_05
private noncomputable def weights : IntegerLookupTree := (.branch 1733 (.branch 1092 (.leaf (139999653600000:ℤ)) (.leaf (27564881500000:ℤ))) (.branch 2323 (.leaf (5134523600000:ℤ)) (.leaf (7018982200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 147 (.leaf (1793071396908557:ℤ)) (.leaf (2156728308503424:ℤ))) (.branch 200 (.leaf (2356742272452128:ℤ)) (.leaf (2907768538671797:ℤ)))), (.branch 163 (.branch 147 (.leaf (1799872837118043:ℤ)) (.leaf (2171267029494923:ℤ))) (.branch 200 (.leaf (2376755510761139:ℤ)) (.leaf (2947222360814818:ℤ)))), (.branch 163 (.branch 147 (.leaf (1794433294385244:ℤ)) (.leaf (2159912754056600:ℤ))) (.branch 200 (.leaf (2361320805440270:ℤ)) (.leaf (2917788842862945:ℤ)))), (.branch 163 (.branch 147 (.leaf (1801513437769046:ℤ)) (.leaf (2175114691963943:ℤ))) (.branch 200 (.leaf (2382297482817240:ℤ)) (.leaf (2959414073489018:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 13 5) 8000 (endpointMeanRuns 13 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 13 5, EndpointRunConditions (endpointMeanCutoff 13 5) (endpointMeanBox 13 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 13 5 h) (endpointMeanCornerA 13 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 5, endpointJoint24Q (endpointMeanCornerK 13 5 h) (endpointMeanCornerA 13 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 13 5, endpointRunWeightQ (endpointMeanCutoff 13 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 13 5) = (455325749/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 13 5 h = (logRoundedQ ((endpointMeanCutoff 13 5:ℚ)/200)).2+(455325749/1000000000000000:ℚ)+((endpointMeanRuns 13 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 13 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 13 5) r*endpointJoint24Q (endpointMeanCornerK 13 5 h) (endpointMeanCornerA 13 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 13 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 13 5 h≤endpointMeanCorner 13 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 13 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint13_05

namespace EndpointAnalyticJoint13_06
private noncomputable def weights : IntegerLookupTree := (.branch 1285 (.branch 1092 (.leaf (135274018700000:ℤ)) (.leaf (8086354800000:ℤ))) (.branch 1733 (.leaf (11948334500000:ℤ)) (.branch 2323 (.leaf (5106380700000:ℤ)) (.leaf (6984951800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 147 (.leaf (1799872837118043:ℤ)) (.leaf (2171267029494923:ℤ))) (.branch 185 (.leaf (2376755510761139:ℤ)) (.branch 200 (.leaf (2698169843673886:ℤ)) (.leaf (2947222360814818:ℤ))))), (.branch 163 (.branch 147 (.leaf (1806700076405584:ℤ)) (.leaf (2185903757457091:ℤ))) (.branch 185 (.leaf (2396938699646542:ℤ)) (.branch 200 (.leaf (2728729161163489:ℤ)) (.leaf (2987211508951295:ℤ))))), (.branch 163 (.branch 147 (.leaf (1801513437769046:ℤ)) (.leaf (2175114691963943:ℤ))) (.branch 185 (.leaf (2382297482817240:ℤ)) (.branch 200 (.leaf (2707093280172097:ℤ)) (.leaf (2959414073489018:ℤ))))), (.branch 163 (.branch 147 (.leaf (1808621516674603:ℤ)) (.leaf (2190423624431928:ℤ))) (.branch 185 (.leaf (2403460505477231:ℤ)) (.branch 200 (.leaf (2739260646831473:ℤ)) (.leaf (3001633130439747:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 13 6) 8000 (endpointMeanRuns 13 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 13 6, EndpointRunConditions (endpointMeanCutoff 13 6) (endpointMeanBox 13 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 13 6 h) (endpointMeanCornerA 13 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 6, endpointJoint24Q (endpointMeanCornerK 13 6 h) (endpointMeanCornerA 13 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 13 6, endpointRunWeightQ (endpointMeanCutoff 13 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 13 6) = (28360191/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 13 6 h = (logRoundedQ ((endpointMeanCutoff 13 6:ℚ)/200)).2+(28360191/62500000000000:ℚ)+((endpointMeanRuns 13 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 13 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 13 6) r*endpointJoint24Q (endpointMeanCornerK 13 6 h) (endpointMeanCornerA 13 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 13 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 13 6 h≤endpointMeanCorner 13 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 13 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint13_06

namespace EndpointAnalyticJoint13_07
private noncomputable def weights : IntegerLookupTree := (.branch 1285 (.branch 1092 (.leaf (131458576900000:ℤ)) (.leaf (8040455600000:ℤ))) (.branch 1733 (.leaf (11886906800000:ℤ)) (.branch 2323 (.leaf (5083216600000:ℤ)) (.leaf (6956941800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 147 (.leaf (1806700076405584:ℤ)) (.leaf (2185903757457091:ℤ))) (.branch 185 (.leaf (2396938699646542:ℤ)) (.branch 200 (.leaf (2728729161163489:ℤ)) (.leaf (2987211508951295:ℤ))))), (.branch 163 (.branch 147 (.leaf (1813553212631689:ℤ)) (.leaf (2200639153064702:ℤ))) (.branch 185 (.leaf (2417293282312982:ℤ)) (.branch 200 (.leaf (2759634591736980:ℤ)) (.leaf (3027743246608649:ℤ))))), (.branch 163 (.branch 147 (.leaf (1808621516674603:ℤ)) (.leaf (2190423624431928:ℤ))) (.branch 185 (.leaf (2403460505477231:ℤ)) (.branch 200 (.leaf (2739260646831473:ℤ)) (.leaf (3001633130439747:ℤ))))), (.branch 163 (.branch 147 (.leaf (1815757641324738:ℤ)) (.leaf (2205840304511649:ℤ))) (.branch 185 (.leaf (2424811528809399:ℤ)) (.branch 200 (.leaf (2771810246155447:ℤ)) (.leaf (3044454485252669:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 13 7) 8000 (endpointMeanRuns 13 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 13 7, EndpointRunConditions (endpointMeanCutoff 13 7) (endpointMeanBox 13 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 13 7 h) (endpointMeanCornerA 13 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 7, endpointJoint24Q (endpointMeanCornerK 13 7 h) (endpointMeanCornerA 13 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 13 7, endpointRunWeightQ (endpointMeanCutoff 13 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 13 7) = (452476823/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 13 7 h = (logRoundedQ ((endpointMeanCutoff 13 7:ℚ)/200)).2+(452476823/1000000000000000:ℚ)+((endpointMeanRuns 13 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 13 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 13 7) r*endpointJoint24Q (endpointMeanCornerK 13 7 h) (endpointMeanCornerA 13 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 13 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 13 7 h≤endpointMeanCorner 13 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 13 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint13_07

namespace EndpointAnalyticJoint13_08
private noncomputable def weights : IntegerLookupTree := (.branch 1733 (.branch 1092 (.leaf (127750965100000:ℤ)) (.branch 1285 (.leaf (7995063500000:ℤ)) (.leaf (11826157900000:ℤ)))) (.branch 2323 (.leaf (5060308500000:ℤ)) (.branch 3522 (.leaf (2042780100000:ℤ)) (.leaf (265950500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 131 (.leaf (1813553212631689:ℤ)) (.branch 147 (.leaf (2007171406138096:ℤ)) (.leaf (2200639153064702:ℤ)))) (.branch 185 (.leaf (2417293282312982:ℤ)) (.branch 200 (.leaf (2759634591736980:ℤ)) (.leaf (3027743246608649:ℤ))))), (.branch 163 (.branch 131 (.leaf (1820432344028075:ℤ)) (.branch 147 (.leaf (2017667778140601:ℤ)) (.leaf (2215473881446224:ℤ)))) (.branch 185 (.leaf (2437820714220655:ℤ)) (.branch 200 (.leaf (2790890055451367:ℤ)) (.leaf (3068824935868893:ℤ))))), (.branch 163 (.branch 131 (.leaf (1815757641324738:ℤ)) (.branch 147 (.leaf (2010697419300076:ℤ)) (.leaf (2205840304511649:ℤ)))) (.branch 185 (.leaf (2424811528809399:ℤ)) (.branch 200 (.leaf (2771810246155447:ℤ)) (.leaf (3044454485252669:ℤ))))), (.branch 163 (.branch 131 (.leaf (1822921922377168:ℤ)) (.branch 147 (.leaf (2021655724467042:ℤ)) (.leaf (2221365490554337:ℤ)))) (.branch 185 (.leaf (2446352222908491:ℤ)) (.branch 200 (.leaf (2804746620070357:ℤ)) (.leaf (3087886730320436:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 13 8) 8000 (endpointMeanRuns 13 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 13 8, EndpointRunConditions (endpointMeanCutoff 13 8) (endpointMeanBox 13 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 13 8 h) (endpointMeanCornerA 13 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 8, endpointJoint24Q (endpointMeanCornerK 13 8 h) (endpointMeanCornerA 13 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 13 8, endpointRunWeightQ (endpointMeanCutoff 13 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 13 8) = (451204803/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 13 8 h = (logRoundedQ ((endpointMeanCutoff 13 8:ℚ)/200)).2+(451204803/1000000000000000:ℚ)+((endpointMeanRuns 13 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 13 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 13 8) r*endpointJoint24Q (endpointMeanCornerK 13 8 h) (endpointMeanCornerA 13 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 13 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 13 8 h≤endpointMeanCorner 13 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 13 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint13_08

namespace EndpointAnalyticJoint13_09
private noncomputable def weights : IntegerLookupTree := (.branch 1733 (.branch 1285 (.branch 1092 (.leaf (123439577200000:ℤ)) (.leaf (7941246900000:ℤ))) (.branch 1517 (.leaf (6155673400000:ℤ)) (.leaf (3351521400000:ℤ)))) (.branch 2323 (.branch 1986 (.leaf (2337236800000:ℤ)) (.leaf (1656333600000:ℤ))) (.branch 3522 (.leaf (2033012400000:ℤ)) (.leaf (264840200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 147 (.branch 131 (.leaf (1820432344028075:ℤ)) (.leaf (2017667778140601:ℤ))) (.branch 155 (.leaf (2215473881446224:ℤ)) (.leaf (2323353027047759:ℤ)))) (.branch 185 (.branch 172 (.leaf (2437820714220655:ℤ)) (.leaf (2575104763096843:ℤ))) (.branch 200 (.leaf (2790890055451367:ℤ)) (.leaf (3068824935868893:ℤ))))), (.branch 163 (.branch 147 (.branch 131 (.leaf (1827337569199067:ℤ)) (.leaf (2028219040236133:ℤ))) (.branch 155 (.leaf (2230408612213795:ℤ)) (.leaf (2340976701707878:ℤ)))) (.branch 185 (.branch 172 (.leaf (2458522463189406:ℤ)) (.leaf (2599797547214929:ℤ))) (.branch 200 (.leaf (2822499516761999:ℤ)) (.leaf (3110464038705857:ℤ))))), (.branch 163 (.branch 147 (.branch 131 (.leaf (1822921922377168:ℤ)) (.leaf (2021655724467042:ℤ))) (.branch 155 (.leaf (2221365490554337:ℤ)) (.leaf (2330458167891560:ℤ)))) (.branch 185 (.branch 172 (.leaf (2446352222908491:ℤ)) (.leaf (2585538844811554:ℤ))) (.branch 200 (.leaf (2804746620070357:ℤ)) (.leaf (3087886730320436:ℤ))))), (.branch 163 (.branch 147 (.branch 131 (.leaf (1830114470926219:ℤ)) (.leaf (2032673752420224:ℤ))) (.branch 155 (.leaf (2236999946248671:ℤ)) (.leaf (2348932536952107:ℤ)))) (.branch 185 (.branch 172 (.leaf (2468084272705438:ℤ)) (.leaf (2611504772772683:ℤ))) (.branch 200 (.leaf (2838074364472543:ℤ)) (.leaf (3131938580614946:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 13 9) 8000 (endpointMeanRuns 13 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 13 9, EndpointRunConditions (endpointMeanCutoff 13 9) (endpointMeanBox 13 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 13 9 h) (endpointMeanCornerA 13 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 9, endpointJoint24Q (endpointMeanCornerK 13 9 h) (endpointMeanCornerA 13 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 13 9, endpointRunWeightQ (endpointMeanCutoff 13 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 13 9) = (7026511/15625000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 13 9 h = (logRoundedQ ((endpointMeanCutoff 13 9:ℚ)/200)).2+(7026511/15625000000000:ℚ)+((endpointMeanRuns 13 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 13 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 13 9) r*endpointJoint24Q (endpointMeanCornerK 13 9 h) (endpointMeanCornerA 13 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 13 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 13 9 h≤endpointMeanCorner 13 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 13 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint13_09

namespace EndpointAnalyticJoint13_10
private noncomputable def weights : IntegerLookupTree := (.branch 1517 (.branch 1092 (.leaf (119957854600000:ℤ)) (.branch 1285 (.leaf (7896932100000:ℤ)) (.leaf (6123993000000:ℤ)))) (.branch 2323 (.branch 1733 (.leaf (3335444400000:ℤ)) (.leaf (5010784400000:ℤ))) (.branch 3522 (.leaf (2024969300000:ℤ)) (.leaf (263926000000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 131 (.leaf (1827337569199067:ℤ)) (.branch 147 (.leaf (2028219040236133:ℤ)) (.leaf (2230408612213795:ℤ)))) (.branch 185 (.branch 172 (.leaf (2458522463189406:ℤ)) (.leaf (2599797547214929:ℤ))) (.branch 200 (.leaf (2822499516761999:ℤ)) (.leaf (3110464038705857:ℤ))))), (.branch 163 (.branch 131 (.leaf (1834268987123020:ℤ)) (.branch 147 (.leaf (2038825479468866:ℤ)) (.leaf (2245444019493499:ℤ)))) (.branch 185 (.branch 172 (.leaf (2479400009503655:ℤ)) (.leaf (2624727111442412:ℤ))) (.branch 200 (.leaf (2854466985025434:ℤ)) (.leaf (3152668118340554:ℤ))))), (.branch 163 (.branch 131 (.leaf (1830114470926219:ℤ)) (.branch 147 (.leaf (2032673752420224:ℤ)) (.leaf (2236999946248671:ℤ)))) (.branch 185 (.branch 172 (.leaf (2468084272705438:ℤ)) (.leaf (2611504772772683:ℤ))) (.branch 200 (.leaf (2838074364472543:ℤ)) (.leaf (3131938580614946:ℤ))))), (.branch 163 (.branch 131 (.leaf (1837335398504564:ℤ)) (.branch 147 (.leaf (2043751828648950:ℤ)) (.leaf (2252744440658336:ℤ)))) (.branch 185 (.branch 172 (.leaf (2490009378099185:ℤ)) (.leaf (2637731470134445:ℤ))) (.branch 200 (.leaf (2871798129869629:ℤ)) (.leaf (3176618875436031:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 13 10) 8000 (endpointMeanRuns 13 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 13 10, EndpointRunConditions (endpointMeanCutoff 13 10) (endpointMeanBox 13 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 13 10 h) (endpointMeanCornerA 13 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 10, endpointJoint24Q (endpointMeanCornerK 13 10 h) (endpointMeanCornerA 13 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 13 10, endpointRunWeightQ (endpointMeanCutoff 13 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 13 10) = (448454873/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 13 10 h = (logRoundedQ ((endpointMeanCutoff 13 10:ℚ)/200)).2+(448454873/1000000000000000:ℚ)+((endpointMeanRuns 13 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 13 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 13 10) r*endpointJoint24Q (endpointMeanCornerK 13 10 h) (endpointMeanCornerA 13 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 13 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 13 10 h≤endpointMeanCorner 13 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 13 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint13_10

namespace EndpointAnalyticJoint13_11
private noncomputable def weights : IntegerLookupTree := (.branch 1517 (.branch 1162 (.branch 1092 (.leaf (115908581500000:ℤ)) (.leaf (2790641800000:ℤ))) (.branch 1285 (.leaf (4250566600000:ℤ)) (.branch 1365 (.leaf (2109914500000:ℤ)) (.leaf (3338049700000:ℤ))))) (.branch 1986 (.branch 1733 (.leaf (3316378200000:ℤ)) (.leaf (2314102700000:ℤ))) (.branch 2323 (.leaf (1640862700000:ℤ)) (.branch 3522 (.leaf (2015430700000:ℤ)) (.leaf (262841900000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 172 (.branch 147 (.branch 131 (.leaf (1834268987123020:ℤ)) (.leaf (2038825479468866:ℤ))) (.branch 155 (.leaf (2245444019493499:ℤ)) (.branch 163 (.leaf (2358734059843956:ℤ)) (.leaf (2479400009503655:ℤ))))) (.branch 185 (.branch 180 (.leaf (2624727111442412:ℤ)) (.leaf (2763168842294197:ℤ))) (.branch 194 (.leaf (2854466985025434:ℤ)) (.branch 200 (.leaf (3028792227623974:ℤ)) (.leaf (3152668118340554:ℤ)))))), (.branch 172 (.branch 147 (.branch 131 (.leaf (1841226697153718:ℤ)) (.leaf (2049487384384029:ℤ))) (.branch 155 (.leaf (2260580781955758:ℤ)) (.branch 163 (.leaf (2376626115505106:ℤ)) (.leaf (2500454846018270:ℤ))))) (.branch 185 (.branch 180 (.leaf (2649895726273365:ℤ)) (.leaf (2792557896026119:ℤ))) (.branch 194 (.leaf (2886796515007958:ℤ)) (.branch 200 (.leaf (3067074860054262:ℤ)) (.leaf (3195444840614946:ℤ)))))), (.branch 172 (.branch 147 (.branch 131 (.leaf (1837335398504564:ℤ)) (.leaf (2043751828648950:ℤ))) (.branch 155 (.leaf (2252744440658336:ℤ)) (.branch 163 (.leaf (2367553358893417:ℤ)) (.leaf (2490009378099185:ℤ))))) (.branch 185 (.branch 180 (.leaf (2637731470134445:ℤ)) (.leaf (2778700639946788:ℤ))) (.branch 194 (.leaf (2871798129869629:ℤ)) (.branch 200 (.leaf (3049854372698228:ℤ)) (.leaf (3176618875436031:ℤ)))))), (.branch 172 (.branch 147 (.branch 131 (.leaf (1844584817084933:ℤ)) (.leaf (2054890280416429:ℤ))) (.branch 155 (.leaf (2268599748259853:ℤ)) (.branch 163 (.leaf (2386321794699451:ℤ)) (.leaf (2512129254089644:ℤ))))) (.branch 185 (.branch 180 (.leaf (2664221555739527:ℤ)) (.leaf (2809686257012883:ℤ))) (.branch 194 (.leaf (2905922622029481:ℤ)) (.branch 200 (.leaf (3090349502660688:ℤ)) (.leaf (3221936580185163:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 13 11) 8000 (endpointMeanRuns 13 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 13 11, EndpointRunConditions (endpointMeanCutoff 13 11) (endpointMeanBox 13 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 13 11 h) (endpointMeanCornerA 13 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 11, endpointJoint24Q (endpointMeanCornerK 13 11 h) (endpointMeanCornerA 13 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 13 11, endpointRunWeightQ (endpointMeanCutoff 13 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 13 11) = (223491073/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 13 11 h = (logRoundedQ ((endpointMeanCutoff 13 11:ℚ)/200)).2+(223491073/500000000000000:ℚ)+((endpointMeanRuns 13 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 13 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 13 11) r*endpointJoint24Q (endpointMeanCornerK 13 11 h) (endpointMeanCornerA 13 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 13 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 13 11 h≤endpointMeanCorner 13 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 13 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint13_11

namespace EndpointAnalyticJoint13_12
private noncomputable def weights : IntegerLookupTree := (.branch 1630 (.branch 1285 (.branch 1162 (.branch 1092 (.leaf (112638096100000:ℤ)) (.leaf (2774896100000:ℤ))) (.branch 1214 (.leaf (1772627300000:ℤ)) (.leaf (2171694200000:ℤ)))) (.branch 1437 (.branch 1365 (.leaf (2098959500000:ℤ)) (.leaf (1584666300000:ℤ))) (.branch 1517 (.leaf (1498906400000:ℤ)) (.leaf (1758997600000:ℤ))))) (.branch 2141 (.branch 1851 (.branch 1733 (.leaf (1242985200000:ℤ)) (.leaf (1118213700000:ℤ))) (.branch 1986 (.leaf (966798000000:ℤ)) (.leaf (803664100000:ℤ)))) (.branch 2800 (.branch 2323 (.leaf (646894200000:ℤ)) (.leaf (967858000000:ℤ))) (.branch 3522 (.leaf (411341000000:ℤ)) (.leaf (261948800000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 167 (.branch 151 (.branch 139 (.branch 131 (.leaf (1841226697153718:ℤ)) (.leaf (2049487384384029:ℤ))) (.branch 147 (.leaf (2151716730983178:ℤ)) (.leaf (2260580781955758:ℤ)))) (.branch 159 (.branch 155 (.leaf (2317669532975891:ℤ)) (.leaf (2376626115505106:ℤ))) (.branch 163 (.leaf (2437527575431643:ℤ)) (.leaf (2500454846018270:ℤ))))) (.branch 185 (.branch 176 (.branch 172 (.leaf (2565492981540469:ℤ)) (.leaf (2649895726273365:ℤ))) (.branch 180 (.leaf (2720017362966324:ℤ)) (.leaf (2792557896026119:ℤ)))) (.branch 194 (.branch 190 (.leaf (2886796515007958:ℤ)) (.leaf (2985198769165846:ℤ))) (.branch 200 (.leaf (3067074860054262:ℤ)) (.leaf (3195444840614946:ℤ)))))), (.branch 167 (.branch 151 (.branch 139 (.branch 131 (.leaf (1848210799021825:ℤ)) (.leaf (2060205045035800:ℤ))) (.branch 147 (.leaf (2164533439054223:ℤ)) (.leaf (2275819582845984:ℤ)))) (.branch 159 (.branch 155 (.leaf (2334253990525666:ℤ)) (.leaf (2394653890432461:ℤ))) (.branch 163 (.leaf (2457102777689008:ℤ)) (.leaf (2521688478265302:ℤ))))) (.branch 185 (.branch 176 (.branch 172 (.leaf (2588503415878456:ℤ)) (.leaf (2675305683973737:ℤ))) (.branch 180 (.leaf (2747500123856334:ℤ)) (.leaf (2822259531626377:ℤ)))) (.branch 194 (.branch 190 (.leaf (2919492207399915:ℤ)) (.leaf (3021152945184408:ℤ))) (.branch 200 (.leaf (3105841368510252:ℤ)) (.leaf (3238801975384359:ℤ)))))), (.branch 167 (.branch 151 (.branch 139 (.branch 131 (.leaf (1844584817084933:ℤ)) (.leaf (2054890280416429:ℤ))) (.branch 147 (.leaf (2158317218144818:ℤ)) (.leaf (2268599748259853:ℤ)))) (.branch 159 (.branch 155 (.leaf (2326492003833485:ℤ)) (.leaf (2386321794699451:ℤ))) (.branch 163 (.leaf (2448171848299184:ℤ)) (.leaf (2512129254089644:ℤ))))) (.branch 185 (.branch 176 (.branch 172 (.leaf (2578285739514997:ℤ)) (.leaf (2664221555739527:ℤ))) (.branch 180 (.leaf (2735687425353324:ℤ)) (.leaf (2809686257012883:ℤ)))) (.branch 194 (.branch 190 (.leaf (2905922622029481:ℤ)) (.leaf (3006535937181416:ℤ))) (.branch 200 (.leaf (3090349502660688:ℤ)) (.leaf (3221936580185163:ℤ)))))), (.branch 167 (.branch 151 (.branch 139 (.branch 131 (.leaf (1851862839081854:ℤ)) (.leaf (2066089436769487:ℤ))) (.branch 147 (.leaf (2171727477479276:ℤ)) (.leaf (2284566648980678:ℤ)))) (.branch 159 (.branch 155 (.leaf (2343881583790394:ℤ)) (.leaf (2405239014557721:ℤ))) (.branch 163 (.leaf (2468728790546622:ℤ)) (.leaf (2534445630911839:ℤ))))) (.branch 185 (.branch 176 (.branch 172 (.leaf (2602489440488128:ℤ)) (.leaf (2690977674730985:ℤ))) (.branch 180 (.leaf (2764651656321751:ℤ)) (.leaf (2841017398332714:ℤ)))) (.branch 194 (.branch 190 (.leaf (2940452602636819:ℤ)) (.leaf (3044553566126313:ℤ))) (.branch 200 (.leaf (3131382315853326:ℤ)) (.leaf (3267900788164377:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 13 12) 8000 (endpointMeanRuns 13 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 13 12, EndpointRunConditions (endpointMeanCutoff 13 12) (endpointMeanBox 13 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 13 12 h) (endpointMeanCornerA 13 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 12, endpointJoint24Q (endpointMeanCornerK 13 12 h) (endpointMeanCornerA 13 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 13 12, endpointRunWeightQ (endpointMeanCutoff 13 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 13 12) = (27860569/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 13 12 h = (logRoundedQ ((endpointMeanCutoff 13 12:ℚ)/200)).2+(27860569/62500000000000:ℚ)+((endpointMeanRuns 13 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 13 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 13 12) r*endpointJoint24Q (endpointMeanCornerK 13 12 h) (endpointMeanCornerA 13 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 13 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 13 12 h≤endpointMeanCorner 13 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 13 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint13_12

namespace EndpointAnalyticJoint13_13
private noncomputable def weights : IntegerLookupTree := (.branch 1583 (.branch 1285 (.branch 1162 (.branch 1092 (.leaf (108834004200000:ℤ)) (.branch 1115 (.leaf (895664200000:ℤ)) (.leaf (1756248000000:ℤ)))) (.branch 1214 (.leaf (1761030600000:ℤ)) (.branch 1241 (.leaf (818583100000:ℤ)) (.leaf (1260451500000:ℤ))))) (.branch 1400 (.branch 1316 (.leaf (808096700000:ℤ)) (.branch 1365 (.leaf (1195194400000:ℤ)) (.leaf (768171800000:ℤ)))) (.branch 1437 (.leaf (752049900000:ℤ)) (.branch 1517 (.leaf (1490101300000:ℤ)) (.leaf (1030356500000:ℤ)))))) (.branch 2323 (.branch 1851 (.branch 1630 (.leaf (635716100000:ℤ)) (.branch 1733 (.leaf (1236101200000:ℤ)) (.leaf (1112189500000:ℤ)))) (.branch 1986 (.leaf (961737300000:ℤ)) (.branch 2141 (.leaf (799580800000:ℤ)) (.leaf (643708000000:ℤ))))) (.branch 3120 (.branch 2539 (.leaf (487435200000:ℤ)) (.branch 2800 (.leaf (342597400000:ℤ)) (.leaf (216497400000:ℤ)))) (.branch 3522 (.leaf (119285200000:ℤ)) (.branch 4747 (.leaf (96678300000:ℤ)) (.leaf (8955200000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 169 (.branch 147 (.branch 135 (.branch 123 (.leaf (1848210799021825:ℤ)) (.branch 131 (.leaf (1962298931910220:ℤ)) (.leaf (2060205045035800:ℤ)))) (.branch 139 (.leaf (2111534204753012:ℤ)) (.branch 143 (.leaf (2164533439054223:ℤ)) (.leaf (2219271253912039:ℤ))))) (.branch 159 (.branch 151 (.leaf (2275819582845984:ℤ)) (.branch 155 (.leaf (2334253990525666:ℤ)) (.leaf (2394653890432461:ℤ)))) (.branch 163 (.leaf (2457102777689008:ℤ)) (.branch 167 (.leaf (2521688478265302:ℤ)) (.leaf (2588503415878456:ℤ)))))) (.branch 185 (.branch 178 (.branch 172 (.leaf (2622777058154889:ℤ)) (.branch 176 (.leaf (2675305683973737:ℤ)) (.leaf (2747500123856334:ℤ)))) (.branch 180 (.leaf (2784552137387824:ℤ)) (.branch 183 (.leaf (2822259531626377:ℤ)) (.leaf (2880081543293330:ℤ))))) (.branch 194 (.branch 188 (.leaf (2919492207399915:ℤ)) (.branch 190 (.leaf (2979941271964560:ℤ)) (.leaf (3021152945184408:ℤ)))) (.branch 198 (.leaf (3105841368510252:ℤ)) (.branch 200 (.leaf (3193666968282537:ℤ)) (.leaf (3238801975384359:ℤ))))))), (.branch 169 (.branch 147 (.branch 135 (.branch 123 (.leaf (1855221392836298:ℤ)) (.branch 131 (.leaf (1971242687287891:ℤ)) (.leaf (2070978752995168:ℤ)))) (.branch 139 (.leaf (2123329049346798:ℤ)) (.branch 143 (.leaf (2177426489890753:ℤ)) (.leaf (2233344706421250:ℤ))))) (.branch 159 (.branch 151 (.leaf (2291161110015418:ℤ)) (.branch 155 (.leaf (2350957120831976:ℤ)) (.leaf (2412818414117529:ℤ)))) (.branch 163 (.leaf (2476835183724205:ℤ)) (.branch 167 (.leaf (2543102424561645:ℤ)) (.leaf (2611720235535846:ℤ)))))) (.branch 185 (.branch 178 (.branch 172 (.leaf (2646943360882427:ℤ)) (.branch 176 (.leaf (2700959298790092:ℤ)) (.leaf (2775260567586317:ℤ)))) (.branch 180 (.leaf (2813421719495835:ℤ)) (.branch 183 (.leaf (2852277073714582:ℤ)) (.leaf (2911896695075313:ℤ))))) (.branch 194 (.branch 188 (.leaf (2952558209335844:ℤ)) (.branch 190 (.leaf (3014965793551560:ℤ)) (.leaf (3057540158622964:ℤ)))) (.branch 198 (.leaf (3145097868977017:ℤ)) (.branch 200 (.leaf (3235995738599981:ℤ)) (.leaf (3282747397928773:ℤ))))))), (.branch 169 (.branch 147 (.branch 135 (.branch 123 (.leaf (1851862839081854:ℤ)) (.branch 131 (.leaf (1967081560962685:ℤ)) (.leaf (2066089436769487:ℤ)))) (.branch 139 (.leaf (2118045347995789:ℤ)) (.branch 143 (.leaf (2171727477479276:ℤ)) (.leaf (2227208937011181:ℤ))))) (.branch 159 (.branch 151 (.leaf (2284566648980678:ℤ)) (.branch 155 (.leaf (2343881583790394:ℤ)) (.leaf (2405239014557721:ℤ)))) (.branch 163 (.leaf (2468728790546622:ℤ)) (.branch 167 (.leaf (2534445630911839:ℤ)) (.leaf (2602489440488128:ℤ)))))) (.branch 185 (.branch 178 (.branch 172 (.leaf (2637416680033213:ℤ)) (.branch 176 (.leaf (2690977674730985:ℤ)) (.leaf (2764651656321751:ℤ)))) (.branch 180 (.leaf (2802490343412694:ℤ)) (.branch 183 (.leaf (2841017398332714:ℤ)) (.leaf (2900133738984757:ℤ))))) (.branch 194 (.branch 188 (.leaf (2940452602636819:ℤ)) (.branch 190 (.leaf (3002335711498091:ℤ)) (.leaf (3044553566126313:ℤ)))) (.branch 198 (.leaf (3131382315853326:ℤ)) (.branch 200 (.leaf (3221530933203539:ℤ)) (.leaf (3267900788164377:ℤ))))))), (.branch 169 (.branch 147 (.branch 135 (.branch 123 (.leaf (1859169577353408:ℤ)) (.branch 131 (.leaf (1976417170562165:ℤ)) (.leaf (2077349628548237:ℤ)))) (.branch 139 (.leaf (2130381053658933:ℤ)) (.branch 143 (.leaf (2185221058697053:ℤ)) (.leaf (2241948371298040:ℤ))))) (.branch 159 (.branch 151 (.leaf (2300645928237569:ℤ)) (.branch 155 (.leaf (2361401143773274:ℤ)) (.leaf (2424306197932208:ℤ)))) (.branch 163 (.leaf (2489458346442427:ℤ)) (.branch 167 (.leaf (2556960254171261:ℤ)) (.leaf (2626920354113380:ℤ)))))) (.branch 185 (.branch 178 (.branch 172 (.leaf (2662857783273283:ℤ)) (.branch 176 (.leaf (2718002498816412:ℤ)) (.leaf (2793922547571545:ℤ)))) (.branch 180 (.leaf (2832944899235286:ℤ)) (.branch 183 (.leaf (2872697916887799:ℤ)) (.leaf (2933735749480507:ℤ))))) (.branch 194 (.branch 188 (.leaf (2975392889957655:ℤ)) (.branch 190 (.leaf (3039373377220776:ℤ)) (.leaf (3083051927761847:ℤ)))) (.branch 198 (.leaf (3172959951486618:ℤ)) (.branch 200 (.leaf (3266410977627845:ℤ)) (.leaf (3314520722400949:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 13 13) 8000 (endpointMeanRuns 13 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 13 13, EndpointRunConditions (endpointMeanCutoff 13 13) (endpointMeanBox 13 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 13 13 h) (endpointMeanCornerA 13 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 13, endpointJoint24Q (endpointMeanCornerK 13 13 h) (endpointMeanCornerA 13 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 13 13, endpointRunWeightQ (endpointMeanCutoff 13 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 13 13) = (27770633/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 13 13 h = (logRoundedQ ((endpointMeanCutoff 13 13:ℚ)/200)).2+(27770633/62500000000000:ℚ)+((endpointMeanRuns 13 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 13 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 13 13) r*endpointJoint24Q (endpointMeanCornerK 13 13 h) (endpointMeanCornerA 13 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 13 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 13 13 h≤endpointMeanCorner 13 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 13 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint13_13

namespace EndpointAnalyticJoint13_14
private noncomputable def weights : IntegerLookupTree := (.branch 1517 (.branch 1285 (.branch 1162 (.branch 1092 (.leaf (105761162400000:ℤ)) (.branch 1115 (.leaf (890610500000:ℤ)) (.leaf (1746501600000:ℤ)))) (.branch 1214 (.leaf (1751476300000:ℤ)) (.branch 1241 (.leaf (814218900000:ℤ)) (.leaf (1253827900000:ℤ))))) (.branch 1400 (.branch 1316 (.leaf (803913500000:ℤ)) (.branch 1365 (.leaf (1189098900000:ℤ)) (.leaf (764313800000:ℤ)))) (.branch 1437 (.leaf (748319700000:ℤ)) (.branch 1476 (.leaf (726946000000:ℤ)) (.leaf (701059500000:ℤ)))))) (.branch 2141 (.branch 1733 (.branch 1583 (.leaf (1025453600000:ℤ)) (.branch 1630 (.leaf (632741100000:ℤ)) (.leaf (1230429500000:ℤ)))) (.branch 1851 (.leaf (1107226200000:ℤ)) (.branch 1986 (.leaf (957567700000:ℤ)) (.leaf (796216700000:ℤ))))) (.branch 2800 (.branch 2323 (.leaf (641082900000:ℤ)) (.branch 2539 (.leaf (485511600000:ℤ)) (.leaf (341291400000:ℤ)))) (.branch 3522 (.branch 3120 (.leaf (215701800000:ℤ)) (.leaf (118863600000:ℤ))) (.branch 4747 (.leaf (96353400000:ℤ)) (.leaf (8927700000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 169 (.branch 147 (.branch 135 (.branch 123 (.leaf (1855221392836298:ℤ)) (.branch 131 (.leaf (1971242687287891:ℤ)) (.leaf (2070978752995168:ℤ)))) (.branch 139 (.leaf (2123329049346798:ℤ)) (.branch 143 (.leaf (2177426489890753:ℤ)) (.leaf (2233344706421250:ℤ))))) (.branch 159 (.branch 151 (.leaf (2291161110015418:ℤ)) (.branch 155 (.leaf (2350957120831976:ℤ)) (.leaf (2412818414117529:ℤ)))) (.branch 163 (.leaf (2476835183724205:ℤ)) (.branch 167 (.leaf (2543102424561645:ℤ)) (.leaf (2611720235535846:ℤ)))))) (.branch 183 (.branch 176 (.branch 172 (.leaf (2646943360882427:ℤ)) (.branch 174 (.leaf (2700959298790092:ℤ)) (.leaf (2737778120967978:ℤ)))) (.branch 178 (.leaf (2775260567586317:ℤ)) (.branch 180 (.leaf (2813421719495835:ℤ)) (.leaf (2852277073714582:ℤ))))) (.branch 190 (.branch 185 (.leaf (2911896695075313:ℤ)) (.branch 188 (.leaf (2952558209335844:ℤ)) (.leaf (3014965793551560:ℤ)))) (.branch 198 (.branch 194 (.leaf (3057540158622964:ℤ)) (.leaf (3145097868977017:ℤ))) (.branch 200 (.leaf (3235995738599981:ℤ)) (.leaf (3282747397928773:ℤ))))))), (.branch 169 (.branch 147 (.branch 135 (.branch 123 (.leaf (1862258579085820:ℤ)) (.branch 131 (.leaf (1980227206465075:ℤ)) (.leaf (2081808801357874:ℤ)))) (.branch 139 (.leaf (2135189778906447:ℤ)) (.branch 143 (.leaf (2190396338228709:ℤ)) (.leaf (2247507405373494:ℤ))))) (.branch 159 (.branch 151 (.leaf (2306606055952166:ℤ)) (.branch 155 (.leaf (2367779773076845:ℤ)) (.leaf (2431120723860954:ℤ)))) (.branch 163 (.leaf (2496726056003249:ℤ)) (.branch 167 (.leaf (2564698216117597:ℤ)) (.leaf (2635145291625028:ℤ)))))) (.branch 183 (.branch 176 (.branch 172 (.leaf (2671332332244987:ℤ)) (.branch 174 (.leaf (2726858907160421:ℤ)) (.leaf (2764729716804600:ℤ)))) (.branch 178 (.leaf (2803301499833623:ℤ)) (.branch 180 (.leaf (2842590614645931:ℤ)) (.leaf (2882613882270996:ℤ))))) (.branch 190 (.branch 185 (.leaf (2944063296588042:ℤ)) (.branch 188 (.leaf (2985998714920469:ℤ)) (.leaf (3050401973288987:ℤ)))) (.branch 198 (.branch 194 (.leaf (3094365625048322:ℤ)) (.leaf (3184850554743045:ℤ))) (.branch 200 (.leaf (3278885533224083:ℤ)) (.leaf (3327289090383257:ℤ))))))), (.branch 169 (.branch 147 (.branch 135 (.branch 123 (.leaf (1859169577353408:ℤ)) (.branch 131 (.leaf (1976417170562165:ℤ)) (.leaf (2077349628548237:ℤ)))) (.branch 139 (.leaf (2130381053658933:ℤ)) (.branch 143 (.leaf (2185221058697053:ℤ)) (.leaf (2241948371298040:ℤ))))) (.branch 159 (.branch 151 (.leaf (2300645928237569:ℤ)) (.branch 155 (.leaf (2361401143773274:ℤ)) (.leaf (2424306197932208:ℤ)))) (.branch 163 (.leaf (2489458346442427:ℤ)) (.branch 167 (.leaf (2556960254171261:ℤ)) (.leaf (2626920354113380:ℤ)))))) (.branch 183 (.branch 176 (.branch 172 (.leaf (2662857783273283:ℤ)) (.branch 174 (.leaf (2718002498816412:ℤ)) (.leaf (2755613906822447:ℤ)))) (.branch 178 (.leaf (2793922547571545:ℤ)) (.branch 180 (.leaf (2832944899235286:ℤ)) (.leaf (2872697916887799:ℤ))))) (.branch 190 (.branch 185 (.leaf (2933735749480507:ℤ)) (.branch 188 (.leaf (2975392889957655:ℤ)) (.leaf (3039373377220776:ℤ)))) (.branch 198 (.branch 194 (.leaf (3083051927761847:ℤ)) (.leaf (3172959951486618:ℤ))) (.branch 200 (.leaf (3266410977627845:ℤ)) (.leaf (3314520722400949:ℤ))))))), (.branch 169 (.branch 147 (.branch 135 (.branch 123 (.leaf (1866505145202961:ℤ)) (.branch 131 (.leaf (1985797086207882:ℤ)) (.leaf (2088671188395880:ℤ)))) (.branch 139 (.leaf (2142788603692346:ℤ)) (.branch 143 (.leaf (2198798479501502:ℤ)) (.leaf (2256785349609391:ℤ))))) (.branch 159 (.branch 151 (.leaf (2316838376975218:ℤ)) (.branch 155 (.leaf (2379051655329868:ℤ)) (.leaf (2443524533636937:ℤ)))) (.branch 163 (.leaf (2510361965398246:ℤ)) (.branch 167 (.leaf (2579674884980395:ℤ)) (.leaf (2651580613353369:ℤ)))))) (.branch 183 (.branch 176 (.branch 172 (.leaf (2688544297008768:ℤ)) (.branch 174 (.leaf (2745298726534690:ℤ)) (.leaf (2784032091251935:ℤ)))) (.branch 178 (.leaf (2823503345884173:ℤ)) (.branch 180 (.leaf (2863730403556066:ℤ)) (.leaf (2904731708624700:ℤ))))) (.branch 190 (.branch 185 (.leaf (2967727085162948:ℤ)) (.branch 188 (.leaf (3010748359511660:ℤ)) (.leaf (3076867950103087:ℤ)))) (.branch 198 (.branch 194 (.leaf (3122037100950025:ℤ)) (.leaf (3215089643563509:ℤ))) (.branch 200 (.leaf (3311916258447304:ℤ)) (.leaf (3361805737498022:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 13 14) 8000 (endpointMeanRuns 13 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 13 14, EndpointRunConditions (endpointMeanCutoff 13 14) (endpointMeanBox 13 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 13 14 h) (endpointMeanCornerA 13 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 14, endpointJoint24Q (endpointMeanCornerK 13 14 h) (endpointMeanCornerA 13 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 13 14, endpointRunWeightQ (endpointMeanCutoff 13 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 13 14) = (44314457/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 13 14 h = (logRoundedQ ((endpointMeanCutoff 13 14:ℚ)/200)).2+(44314457/100000000000000:ℚ)+((endpointMeanRuns 13 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 13 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 13 14) r*endpointJoint24Q (endpointMeanCornerK 13 14 h) (endpointMeanCornerA 13 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 13 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 13 14 h≤endpointMeanCorner 13 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 13 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint13_14

namespace EndpointAnalyticJoint13_15
private noncomputable def weights : IntegerLookupTree := (.branch 1583 (.branch 1241 (.branch 1115 (.branch 1092 (.leaf (102773930100000:ℤ)) (.leaf (885608300000:ℤ))) (.branch 1162 (.leaf (1736854600000:ℤ)) (.branch 1214 (.leaf (1742019400000:ℤ)) (.leaf (809899300000:ℤ))))) (.branch 1365 (.branch 1285 (.leaf (1247272000000:ℤ)) (.branch 1316 (.leaf (799772900000:ℤ)) (.leaf (1183065500000:ℤ)))) (.branch 1437 (.leaf (1559473200000:ℤ)) (.branch 1517 (.leaf (1475666400000:ℤ)) (.leaf (1020600600000:ℤ)))))) (.branch 2323 (.branch 1851 (.branch 1630 (.leaf (629796400000:ℤ)) (.branch 1733 (.leaf (1224815700000:ℤ)) (.leaf (1102313500000:ℤ)))) (.branch 1986 (.leaf (953440700000:ℤ)) (.branch 2141 (.leaf (792886800000:ℤ)) (.leaf (638484600000:ℤ))))) (.branch 3120 (.branch 2539 (.leaf (483607600000:ℤ)) (.branch 2800 (.leaf (339998600000:ℤ)) (.leaf (214914300000:ℤ)))) (.branch 3522 (.leaf (118446400000:ℤ)) (.branch 4747 (.leaf (96031900000:ℤ)) (.leaf (8900500000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 167 (.branch 143 (.branch 131 (.branch 123 (.leaf (1862258579085820:ℤ)) (.leaf (1980227206465075:ℤ))) (.branch 135 (.leaf (2081808801357874:ℤ)) (.branch 139 (.leaf (2135189778906447:ℤ)) (.leaf (2190396338228709:ℤ))))) (.branch 155 (.branch 147 (.leaf (2247507405373494:ℤ)) (.branch 151 (.leaf (2306606055952166:ℤ)) (.leaf (2367779773076845:ℤ)))) (.branch 159 (.leaf (2431120723860954:ℤ)) (.branch 163 (.leaf (2496726056003249:ℤ)) (.leaf (2564698216117597:ℤ)))))) (.branch 185 (.branch 176 (.branch 169 (.leaf (2635145291625028:ℤ)) (.branch 172 (.leaf (2671332332244987:ℤ)) (.leaf (2726858907160421:ℤ)))) (.branch 180 (.leaf (2803301499833623:ℤ)) (.branch 183 (.leaf (2882613882270996:ℤ)) (.leaf (2944063296588042:ℤ))))) (.branch 194 (.branch 188 (.leaf (2985998714920469:ℤ)) (.branch 190 (.leaf (3050401973288987:ℤ)) (.leaf (3094365625048322:ℤ)))) (.branch 198 (.leaf (3184850554743045:ℤ)) (.branch 200 (.leaf (3278885533224083:ℤ)) (.leaf (3327289090383257:ℤ))))))), (.branch 167 (.branch 143 (.branch 131 (.branch 123 (.leaf (1869322458640250:ℤ)) (.leaf (1989252675234802:ℤ))) (.branch 135 (.leaf (2092695484752385:ℤ)) (.branch 139 (.leaf (2147116761459585:ℤ)) (.leaf (2203443441512675:ℤ))))) (.branch 155 (.branch 147 (.leaf (2261759916722825:ℤ)) (.branch 151 (.leaf (2322155117812470:ℤ)) (.leaf (2384722802518746:ℤ)))) (.branch 159 (.leaf (2449561864831792:ℤ)) (.branch 163 (.leaf (2516776667130733:ℤ)) (.leaf (2586477397146354:ℤ)))))) (.branch 185 (.branch 176 (.branch 169 (.leaf (2658780451861400:ℤ)) (.branch 172 (.leaf (2695946023914342:ℤ)) (.leaf (2753006867926889:ℤ)))) (.branch 180 (.leaf (2831625754623859:ℤ)) (.branch 183 (.leaf (2913273353012601:ℤ)) (.leaf (2976585230161358:ℤ))))) (.branch 194 (.branch 188 (.leaf (3019817965760721:ℤ)) (.branch 190 (.leaf (3086254649570774:ℤ)) (.leaf (3131634622844360:ℤ)))) (.branch 198 (.leaf (3225105697377329:ℤ)) (.branch 200 (.leaf (3322343787954902:ℤ)) (.leaf (3372435143187849:ℤ))))))), (.branch 167 (.branch 143 (.branch 131 (.branch 123 (.leaf (1866505145202961:ℤ)) (.leaf (1985797086207882:ℤ))) (.branch 135 (.leaf (2088671188395880:ℤ)) (.branch 139 (.leaf (2142788603692346:ℤ)) (.leaf (2198798479501502:ℤ))))) (.branch 155 (.branch 147 (.leaf (2256785349609391:ℤ)) (.branch 151 (.leaf (2316838376975218:ℤ)) (.leaf (2379051655329868:ℤ)))) (.branch 159 (.leaf (2443524533636937:ℤ)) (.branch 163 (.leaf (2510361965398246:ℤ)) (.leaf (2579674884980395:ℤ)))))) (.branch 185 (.branch 176 (.branch 169 (.leaf (2651580613353369:ℤ)) (.branch 172 (.leaf (2688544297008768:ℤ)) (.leaf (2745298726534690:ℤ)))) (.branch 180 (.leaf (2823503345884173:ℤ)) (.branch 183 (.leaf (2904731708624700:ℤ)) (.leaf (2967727085162948:ℤ))))) (.branch 194 (.branch 188 (.leaf (3010748359511660:ℤ)) (.branch 190 (.leaf (3076867950103087:ℤ)) (.leaf (3122037100950025:ℤ)))) (.branch 198 (.leaf (3215089643563509:ℤ)) (.branch 200 (.leaf (3311916258447304:ℤ)) (.leaf (3361805737498022:ℤ))))))), (.branch 167 (.branch 143 (.branch 131 (.branch 123 (.leaf (1873869656380942:ℤ)) (.leaf (1995221518172746:ℤ))) (.branch 135 (.leaf (2100054450768524:ℤ)) (.branch 139 (.leaf (2155268416524733:ℤ)) (.leaf (2212460260812625:ℤ))))) (.branch 155 (.branch 147 (.leaf (2271720517481316:ℤ)) (.branch 151 (.leaf (2333144791705155:ℤ)) (.leaf (2396834097269840:ℤ)))) (.branch 159 (.leaf (2462895219910079:ℤ)) (.branch 163 (.leaf (2531441108996238:ℤ)) (.leaf (2602591300096477:ℤ)))))) (.branch 185 (.branch 176 (.branch 169 (.leaf (2676472371193925:ℤ)) (.branch 172 (.leaf (2714478588523457:ℤ)) (.leaf (2772869083525468:ℤ)))) (.branch 180 (.leaf (2853397332416553:ℤ)) (.branch 183 (.leaf (2937122712934157:ℤ)) (.leaf (3002112256896124:ℤ))))) (.branch 194 (.branch 188 (.leaf (3046523944752433:ℤ)) (.branch 190 (.leaf (3114825066681468:ℤ)) (.leaf (3161515241420010:ℤ)))) (.branch 198 (.leaf (3257778722138068:ℤ)) (.branch 200 (.leaf (3358055486004209:ℤ)) (.leaf (3409765321511683:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 13 15) 8000 (endpointMeanRuns 13 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 13 15, EndpointRunConditions (endpointMeanCutoff 13 15) (endpointMeanBox 13 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 13 15 h) (endpointMeanCornerA 13 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 15, endpointJoint24Q (endpointMeanCornerK 13 15 h) (endpointMeanCornerA 13 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 13 15, endpointRunWeightQ (endpointMeanCutoff 13 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 13 15) = (220985549/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 13 15 h = (logRoundedQ ((endpointMeanCutoff 13 15:ℚ)/200)).2+(220985549/500000000000000:ℚ)+((endpointMeanRuns 13 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 13 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 13 15) r*endpointJoint24Q (endpointMeanCornerK 13 15 h) (endpointMeanCornerA 13 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 13 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 13 15 h≤endpointMeanCorner 13 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 13 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint13_15

namespace EndpointAnalyticJoint13_16
private noncomputable def weights : IntegerLookupTree := (.branch 1517 (.branch 1214 (.branch 1092 (.leaf (99298710800000:ℤ)) (.branch 1162 (.leaf (2707520500000:ℤ)) (.leaf (1730796800000:ℤ)))) (.branch 1365 (.branch 1285 (.leaf (2121748000000:ℤ)) (.leaf (2052083300000:ℤ))) (.branch 1437 (.leaf (1550236100000:ℤ)) (.leaf (1467145300000:ℤ))))) (.branch 1986 (.branch 1733 (.branch 1630 (.leaf (1722780000000:ℤ)) (.leaf (1218153800000:ℤ))) (.branch 1851 (.leaf (1096483600000:ℤ)) (.leaf (948543200000:ℤ)))) (.branch 2800 (.branch 2323 (.leaf (1604367200000:ℤ)) (.leaf (951416000000:ℤ))) (.branch 3522 (.leaf (404826000000:ℤ)) (.leaf (258127700000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 167 (.branch 147 (.branch 131 (.leaf (1869322458640250:ℤ)) (.branch 139 (.leaf (2092695484752385:ℤ)) (.leaf (2203443441512675:ℤ)))) (.branch 159 (.branch 155 (.leaf (2322155117812470:ℤ)) (.leaf (2449561864831792:ℤ))) (.branch 163 (.leaf (2516776667130733:ℤ)) (.leaf (2586477397146354:ℤ))))) (.branch 185 (.branch 176 (.branch 172 (.leaf (2658780451861400:ℤ)) (.leaf (2753006867926889:ℤ))) (.branch 180 (.leaf (2831625754623859:ℤ)) (.leaf (2913273353012601:ℤ)))) (.branch 194 (.branch 190 (.leaf (3019817965760721:ℤ)) (.leaf (3131634622844360:ℤ))) (.branch 200 (.leaf (3225105697377329:ℤ)) (.leaf (3372435143187849:ℤ)))))), (.branch 167 (.branch 147 (.branch 131 (.leaf (1876413132752063:ℤ)) (.branch 139 (.leaf (2103639099347899:ℤ)) (.leaf (2216568259911992:ℤ)))) (.branch 159 (.branch 155 (.leaf (2337808997452176:ℤ)) (.leaf (2468142890127155:ℤ))) (.branch 163 (.leaf (2536988299931230:ℤ)) (.leaf (2608441524974426:ℤ))))) (.branch 185 (.branch 176 (.branch 172 (.leaf (2682627600712280:ℤ)) (.leaf (2779405562550704:ℤ))) (.branch 180 (.leaf (2860236194617317:ℤ)) (.leaf (2944258917773234:ℤ)))) (.branch 194 (.branch 190 (.leaf (3054020251503731:ℤ)) (.leaf (3169352493968576:ℤ))) (.branch 200 (.leaf (3265869647718808:ℤ)) (.leaf (3418193756557051:ℤ)))))), (.branch 167 (.branch 147 (.branch 131 (.leaf (1873869656380942:ℤ)) (.branch 139 (.leaf (2100054450768524:ℤ)) (.leaf (2212460260812625:ℤ)))) (.branch 159 (.branch 155 (.leaf (2333144791705155:ℤ)) (.leaf (2462895219910079:ℤ))) (.branch 163 (.leaf (2531441108996238:ℤ)) (.leaf (2602591300096477:ℤ))))) (.branch 185 (.branch 176 (.branch 172 (.leaf (2676472371193925:ℤ)) (.leaf (2772869083525468:ℤ))) (.branch 180 (.leaf (2853397332416553:ℤ)) (.leaf (2937122712934157:ℤ)))) (.branch 194 (.branch 190 (.leaf (3046523944752433:ℤ)) (.leaf (3161515241420010:ℤ))) (.branch 200 (.leaf (3257778722138068:ℤ)) (.leaf (3409765321511683:ℤ)))))), (.branch 167 (.branch 147 (.branch 131 (.leaf (1881263225086586:ℤ)) (.branch 139 (.leaf (2111499751945053:ℤ)) (.leaf (2226206926787042:ℤ)))) (.branch 159 (.branch 155 (.leaf (2349565974544940:ℤ)) (.leaf (2482419464488660:ℤ))) (.branch 163 (.leaf (2552697251091239:ℤ)) (.leaf (2625711292060494:ℤ))))) (.branch 185 (.branch 176 (.branch 172 (.leaf (2701597800832074:ℤ)) (.leaf (2800716322801313:ℤ))) (.branch 180 (.leaf (2883607823065039:ℤ)) (.leaf (2969874913135487:ℤ)))) (.branch 194 (.branch 190 (.leaf (3082724637755958:ℤ)) (.leaf (3201492582740143:ℤ))) (.branch 200 (.leaf (3301034614590800:ℤ)) (.leaf (3458409097854814:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 13 16) 8000 (endpointMeanRuns 13 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 13 16, EndpointRunConditions (endpointMeanCutoff 13 16) (endpointMeanBox 13 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 13 16 h) (endpointMeanCornerA 13 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 16, endpointJoint24Q (endpointMeanCornerK 13 16 h) (endpointMeanCornerA 13 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 13 16, endpointRunWeightQ (endpointMeanCutoff 13 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 13 16) = (220289271/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 13 16 h = (logRoundedQ ((endpointMeanCutoff 13 16:ℚ)/200)).2+(220289271/500000000000000:ℚ)+((endpointMeanRuns 13 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 13 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 13 16) r*endpointJoint24Q (endpointMeanCornerK 13 16 h) (endpointMeanCornerA 13 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 13 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 13 16 h≤endpointMeanCorner 13 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 13 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint13_16

namespace EndpointAnalyticJoint13_17
private noncomputable def weights : IntegerLookupTree := (.branch 1517 (.branch 1162 (.branch 1092 (.leaf (96491057900000:ℤ)) (.leaf (2692622400000:ℤ))) (.branch 1285 (.leaf (4107323600000:ℤ)) (.branch 1365 (.leaf (2041718000000:ℤ)) (.leaf (3234236900000:ℤ))))) (.branch 1986 (.branch 1733 (.leaf (3218617200000:ℤ)) (.leaf (2249748300000:ℤ))) (.branch 2323 (.leaf (1597826000000:ℤ)) (.branch 3522 (.leaf (1966522000000:ℤ)) (.leaf (257282800000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 172 (.branch 147 (.branch 131 (.leaf (1876413132752063:ℤ)) (.leaf (2103639099347899:ℤ))) (.branch 155 (.leaf (2337808997452176:ℤ)) (.branch 163 (.leaf (2468142890127155:ℤ)) (.leaf (2608441524974426:ℤ))))) (.branch 185 (.branch 180 (.leaf (2779405562550704:ℤ)) (.leaf (2944258917773234:ℤ))) (.branch 194 (.leaf (3054020251503731:ℤ)) (.branch 200 (.leaf (3265869647718808:ℤ)) (.leaf (3418193756557051:ℤ)))))), (.branch 172 (.branch 147 (.branch 131 (.leaf (1883530703057803:ℤ)) (.leaf (2114639942862430:ℤ))) (.branch 155 (.leaf (2353568401458408:ℤ)) (.branch 163 (.leaf (2486864860832385:ℤ)) (.leaf (2630592170153001:ℤ))))) (.branch 185 (.branch 180 (.leaf (2806057395329013:ℤ)) (.leaf (2975574044887678:ℤ))) (.branch 194 (.leaf (3088609910380922:ℤ)) (.branch 200 (.leaf (3307148836878284:ℤ)) (.leaf (3464573241969321:ℤ)))))), (.branch 172 (.branch 147 (.branch 131 (.leaf (1881263225086586:ℤ)) (.leaf (2111499751945053:ℤ))) (.branch 155 (.leaf (2349565974544940:ℤ)) (.branch 163 (.leaf (2482419464488660:ℤ)) (.leaf (2625711292060494:ℤ))))) (.branch 185 (.branch 180 (.leaf (2800716322801313:ℤ)) (.leaf (2969874913135487:ℤ))) (.branch 194 (.leaf (3082724637755958:ℤ)) (.branch 200 (.leaf (3301034614590800:ℤ)) (.leaf (3458409097854814:ℤ)))))), (.branch 172 (.branch 147 (.branch 131 (.leaf (1888685965969717:ℤ)) (.leaf (2123007430037084:ℤ))) (.branch 155 (.leaf (2366102733257606:ℤ)) (.branch 163 (.leaf (2502098484683876:ℤ)) (.leaf (2649036669337369:ℤ))))) (.branch 185 (.branch 180 (.leaf (2828843225022626:ℤ)) (.leaf (3002992336966503:ℤ))) (.branch 194 (.leaf (3119355489917164:ℤ)) (.branch 200 (.leaf (3344864846920937:ℤ)) (.leaf (3507746827228085:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 13 17) 8000 (endpointMeanRuns 13 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 13 17, EndpointRunConditions (endpointMeanCutoff 13 17) (endpointMeanBox 13 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 13 17 h) (endpointMeanCornerA 13 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 13 17, endpointJoint24Q (endpointMeanCornerK 13 17 h) (endpointMeanCornerA 13 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 13 17, endpointRunWeightQ (endpointMeanCutoff 13 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 13 17) = (439430809/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 13 17 h = (logRoundedQ ((endpointMeanCutoff 13 17:ℚ)/200)).2+(439430809/1000000000000000:ℚ)+((endpointMeanRuns 13 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 13 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 13 17) r*endpointJoint24Q (endpointMeanCornerK 13 17 h) (endpointMeanCornerA 13 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 13 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 13 17 h≤endpointMeanCorner 13 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 13 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint13_17

namespace EndpointAnalyticJoint14_03
private noncomputable def weights : IntegerLookupTree := (.branch 1684 (.branch 1061 (.leaf (146028285700000:ℤ)) (.leaf (30999242500000:ℤ))) (.branch 2257 (.leaf (6079723200000:ℤ)) (.leaf (8443631700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 147 (.leaf (1780851580611278:ℤ)) (.leaf (2130882111046392:ℤ))) (.branch 200 (.leaf (2321369466672394:ℤ)) (.leaf (2839125461706161:ℤ)))), (.branch 163 (.branch 147 (.leaf (1787380976733567:ℤ)) (.leaf (2144817062921890:ℤ))) (.branch 200 (.leaf (2340528832533225:ℤ)) (.leaf (2876749086179229:ℤ)))), (.branch 163 (.branch 147 (.leaf (1781705136399604:ℤ)) (.leaf (2132887387298959:ℤ))) (.branch 200 (.leaf (2324258461028156:ℤ)) (.leaf (2845475264341919:ℤ)))), (.branch 163 (.branch 147 (.leaf (1788497032827613:ℤ)) (.leaf (2147446725852081:ℤ))) (.branch 200 (.leaf (2344324003923558:ℤ)) (.leaf (2885133210836184:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 14 3) 8000 (endpointMeanRuns 14 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 14 3, EndpointRunConditions (endpointMeanCutoff 14 3) (endpointMeanBox 14 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 14 3 h) (endpointMeanCornerA 14 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 3, endpointJoint24Q (endpointMeanCornerK 14 3 h) (endpointMeanCornerA 14 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 14 3, endpointRunWeightQ (endpointMeanCutoff 14 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 14 3) = (228855149/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 14 3 h = (logRoundedQ ((endpointMeanCutoff 14 3:ℚ)/200)).2+(228855149/500000000000000:ℚ)+((endpointMeanRuns 14 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 14 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 14 3) r*endpointJoint24Q (endpointMeanCornerK 14 3 h) (endpointMeanCornerA 14 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 14 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 14 3 h≤endpointMeanCorner 14 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 14 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint14_03

namespace EndpointAnalyticJoint14_04
private noncomputable def weights : IntegerLookupTree := (.branch 1684 (.branch 1061 (.leaf (141876862100000:ℤ)) (.leaf (30825393800000:ℤ))) (.branch 2257 (.leaf (6051265700000:ℤ)) (.leaf (8408710100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 147 (.leaf (1787380976733567:ℤ)) (.leaf (2144817062921890:ℤ))) (.branch 200 (.leaf (2340528832533225:ℤ)) (.leaf (2876749086179229:ℤ)))), (.branch 163 (.branch 147 (.leaf (1794433294385244:ℤ)) (.leaf (2159912754056600:ℤ))) (.branch 200 (.leaf (2361320805440270:ℤ)) (.leaf (2917788842862945:ℤ)))), (.branch 163 (.branch 147 (.leaf (1788497032827613:ℤ)) (.leaf (2147446725852081:ℤ))) (.branch 200 (.leaf (2344324003923558:ℤ)) (.leaf (2885133210836184:ℤ)))), (.branch 163 (.branch 147 (.leaf (1795833978212036:ℤ)) (.leaf (2163223475054663:ℤ))) (.branch 200 (.leaf (2366107882143539:ℤ)) (.leaf (2928422378412706:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 14 4) 8000 (endpointMeanRuns 14 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 14 4, EndpointRunConditions (endpointMeanCutoff 14 4) (endpointMeanBox 14 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 14 4 h) (endpointMeanCornerA 14 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 4, endpointJoint24Q (endpointMeanCornerK 14 4 h) (endpointMeanCornerA 14 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 14 4, endpointRunWeightQ (endpointMeanCutoff 14 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 14 4) = (91275891/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 14 4 h = (logRoundedQ ((endpointMeanCutoff 14 4:ℚ)/200)).2+(91275891/200000000000000:ℚ)+((endpointMeanRuns 14 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 14 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 14 4) r*endpointJoint24Q (endpointMeanCornerK 14 4 h) (endpointMeanCornerA 14 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 14 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 14 4 h≤endpointMeanCorner 14 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 14 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint14_04

namespace EndpointAnalyticJoint14_05
private noncomputable def weights : IntegerLookupTree := (.branch 1684 (.branch 1061 (.leaf (137050919700000:ℤ)) (.leaf (30619394200000:ℤ))) (.branch 2257 (.leaf (6017545300000:ℤ)) (.leaf (8367330100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 147 (.leaf (1794433294385244:ℤ)) (.leaf (2159912754056600:ℤ))) (.branch 200 (.leaf (2361320805440270:ℤ)) (.leaf (2917788842862945:ℤ)))), (.branch 163 (.branch 147 (.leaf (1801513437769046:ℤ)) (.leaf (2175114691963943:ℤ))) (.branch 200 (.leaf (2382297482817240:ℤ)) (.leaf (2959414073489018:ℤ)))), (.branch 163 (.branch 147 (.leaf (1795833978212036:ℤ)) (.leaf (2163223475054663:ℤ))) (.branch 200 (.leaf (2366107882143539:ℤ)) (.leaf (2928422378412706:ℤ)))), (.branch 163 (.branch 147 (.leaf (1803201021922919:ℤ)) (.leaf (2179116132052494:ℤ))) (.branch 200 (.leaf (2388094180058709:ℤ)) (.leaf (2972361066095418:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 14 5) 8000 (endpointMeanRuns 14 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 14 5, EndpointRunConditions (endpointMeanCutoff 14 5) (endpointMeanBox 14 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 14 5 h) (endpointMeanCornerA 14 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 5, endpointJoint24Q (endpointMeanCornerK 14 5 h) (endpointMeanCornerA 14 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 14 5, endpointRunWeightQ (endpointMeanCutoff 14 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 14 5) = (45480249/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 14 5 h = (logRoundedQ ((endpointMeanCutoff 14 5:ℚ)/200)).2+(45480249/100000000000000:ℚ)+((endpointMeanRuns 14 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 14 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 14 5) r*endpointJoint24Q (endpointMeanCornerK 14 5 h) (endpointMeanCornerA 14 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 14 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 14 5 h≤endpointMeanCorner 14 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 14 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint14_05

namespace EndpointAnalyticJoint14_06
private noncomputable def weights : IntegerLookupTree := (.branch 1234 (.branch 1061 (.leaf (133154865500000:ℤ)) (.leaf (8310268300000:ℤ))) (.branch 1684 (.leaf (14472625500000:ℤ)) (.branch 2257 (.leaf (5989793700000:ℤ)) (.leaf (8333274700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 147 (.leaf (1801513437769046:ℤ)) (.leaf (2175114691963943:ℤ))) (.branch 186 (.leaf (2382297482817240:ℤ)) (.branch 200 (.leaf (2723083000986276:ℤ)) (.leaf (2959414073489018:ℤ))))), (.branch 163 (.branch 147 (.leaf (1808621516674603:ℤ)) (.leaf (2190423624431928:ℤ))) (.branch 186 (.leaf (2403460505477231:ℤ)) (.branch 200 (.leaf (2755848765813537:ℤ)) (.leaf (3001633130439747:ℤ))))), (.branch 163 (.branch 147 (.leaf (1803201021922919:ℤ)) (.leaf (2179116132052494:ℤ))) (.branch 186 (.leaf (2388094180058709:ℤ)) (.branch 200 (.leaf (2732702481482593:ℤ)) (.leaf (2972361066095418:ℤ))))), (.branch 163 (.branch 147 (.leaf (1810598287432534:ℤ)) (.leaf (2195125548390891:ℤ))) (.branch 186 (.leaf (2410284778589106:ℤ)) (.branch 200 (.leaf (2767209871864589:ℤ)) (.leaf (3016959019425568:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 14 6) 8000 (endpointMeanRuns 14 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 14 6, EndpointRunConditions (endpointMeanCutoff 14 6) (endpointMeanBox 14 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 14 6 h) (endpointMeanCornerA 14 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 6, endpointJoint24Q (endpointMeanCornerK 14 6 h) (endpointMeanCornerA 14 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 14 6, endpointRunWeightQ (endpointMeanCutoff 14 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 14 6) = (453504657/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 14 6 h = (logRoundedQ ((endpointMeanCutoff 14 6:ℚ)/200)).2+(453504657/1000000000000000:ℚ)+((endpointMeanRuns 14 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 14 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 14 6) r*endpointJoint24Q (endpointMeanCornerK 14 6 h) (endpointMeanCornerA 14 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 14 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 14 6 h≤endpointMeanCorner 14 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 14 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint14_06

namespace EndpointAnalyticJoint14_07
private noncomputable def weights : IntegerLookupTree := (.branch 1234 (.branch 1061 (.leaf (128625077800000:ℤ)) (.leaf (8252823100000:ℤ))) (.branch 1684 (.leaf (14382046400000:ℤ)) (.branch 2257 (.leaf (5956899500000:ℤ)) (.leaf (8292908500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 147 (.leaf (1808621516674603:ℤ)) (.leaf (2190423624431928:ℤ))) (.branch 186 (.leaf (2403460505477231:ℤ)) (.branch 200 (.leaf (2755848765813537:ℤ)) (.leaf (3001633130439747:ℤ))))), (.branch 163 (.branch 147 (.leaf (1815757641324738:ℤ)) (.leaf (2205840304511649:ℤ))) (.branch 186 (.leaf (2424811528809399:ℤ)) (.branch 200 (.leaf (2789008787938258:ℤ)) (.leaf (3044454485252669:ℤ))))), (.branch 163 (.branch 147 (.leaf (1810598287432534:ℤ)) (.leaf (2195125548390891:ℤ))) (.branch 186 (.leaf (2410284778589106:ℤ)) (.branch 200 (.leaf (2767209871864589:ℤ)) (.leaf (3016959019425568:ℤ))))), (.branch 163 (.branch 147 (.leaf (1818025898719658:ℤ)) (.leaf (2211252581871267:ℤ))) (.branch 186 (.leaf (2432681576132617:ℤ)) (.branch 200 (.leaf (2802153006715310:ℤ)) (.leaf (3062226130168636:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 14 7) 8000 (endpointMeanRuns 14 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 14 7, EndpointRunConditions (endpointMeanCutoff 14 7) (endpointMeanBox 14 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 14 7 h) (endpointMeanCornerA 14 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 7, endpointJoint24Q (endpointMeanCornerK 14 7 h) (endpointMeanCornerA 14 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 14 7, endpointRunWeightQ (endpointMeanCutoff 14 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 14 7) = (451966327/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 14 7 h = (logRoundedQ ((endpointMeanCutoff 14 7:ℚ)/200)).2+(451966327/1000000000000000:ℚ)+((endpointMeanRuns 14 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 14 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 14 7) r*endpointJoint24Q (endpointMeanCornerK 14 7 h) (endpointMeanCornerA 14 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 14 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 14 7 h≤endpointMeanCorner 14 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 14 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint14_07

namespace EndpointAnalyticJoint14_08
private noncomputable def weights : IntegerLookupTree := (.branch 1684 (.branch 1061 (.leaf (124248544600000:ℤ)) (.branch 1234 (.leaf (8196135500000:ℤ)) (.leaf (14292661800000:ℤ)))) (.branch 2257 (.leaf (5924439000000:ℤ)) (.branch 3422 (.leaf (2499012600000:ℤ)) (.leaf (349062900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 131 (.leaf (1815757641324738:ℤ)) (.branch 147 (.leaf (2010697419300076:ℤ)) (.leaf (2205840304511649:ℤ)))) (.branch 186 (.leaf (2424811528809399:ℤ)) (.branch 200 (.leaf (2789008787938258:ℤ)) (.leaf (3044454485252669:ℤ))))), (.branch 163 (.branch 131 (.leaf (1822921922377168:ℤ)) (.branch 147 (.leaf (2021655724467042:ℤ)) (.leaf (2221365490554337:ℤ)))) (.branch 186 (.leaf (2446352222908491:ℤ)) (.branch 200 (.leaf (2822567811300256:ℤ)) (.leaf (3087886730320436:ℤ))))), (.branch 163 (.branch 131 (.leaf (1818025898719658:ℤ)) (.branch 147 (.leaf (2014346416967517:ℤ)) (.leaf (2211252581871267:ℤ)))) (.branch 186 (.leaf (2432681576132617:ℤ)) (.branch 200 (.leaf (2802153006715310:ℤ)) (.leaf (3062226130168636:ℤ))))), (.branch 163 (.branch 131 (.leaf (1825483980271676:ℤ)) (.branch 147 (.leaf (2025783687680006:ℤ)) (.leaf (2227498096597093:ℤ)))) (.branch 186 (.leaf (2455286488727365:ℤ)) (.branch 200 (.leaf (2837537388428299:ℤ)) (.leaf (3108172438508295:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 14 8) 8000 (endpointMeanRuns 14 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 14 8, EndpointRunConditions (endpointMeanCutoff 14 8) (endpointMeanBox 14 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 14 8 h) (endpointMeanCornerA 14 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 8, endpointJoint24Q (endpointMeanCornerK 14 8 h) (endpointMeanCornerA 14 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 14 8, endpointRunWeightQ (endpointMeanCutoff 14 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 14 8) = (112612071/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 14 8 h = (logRoundedQ ((endpointMeanCutoff 14 8:ℚ)/200)).2+(112612071/250000000000000:ℚ)+((endpointMeanRuns 14 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 14 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 14 8) r*endpointJoint24Q (endpointMeanCornerK 14 8 h) (endpointMeanCornerA 14 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 14 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 14 8 h≤endpointMeanCorner 14 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 14 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint14_08

namespace EndpointAnalyticJoint14_09
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1061 (.leaf (120714497900000:ℤ)) (.branch 1234 (.leaf (8149460200000:ℤ)) (.leaf (7666979800000:ℤ)))) (.branch 2257 (.branch 1684 (.leaf (3866121100000:ℤ)) (.leaf (5897711900000:ℤ))) (.branch 3422 (.leaf (2488987500000:ℤ)) (.leaf (347842400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 131 (.leaf (1822921922377168:ℤ)) (.branch 147 (.leaf (2021655724467042:ℤ)) (.leaf (2221365490554337:ℤ)))) (.branch 186 (.branch 172 (.leaf (2446352222908491:ℤ)) (.leaf (2585538844811554:ℤ))) (.branch 200 (.leaf (2822567811300256:ℤ)) (.leaf (3087886730320436:ℤ))))), (.branch 163 (.branch 131 (.leaf (1830114470926219:ℤ)) (.branch 147 (.leaf (2032673752420224:ℤ)) (.leaf (2236999946248671:ℤ)))) (.branch 186 (.branch 172 (.leaf (2468084272705438:ℤ)) (.leaf (2611504772772683:ℤ))) (.branch 200 (.leaf (2856530636921279:ℤ)) (.leaf (3131938580614946:ℤ))))), (.branch 163 (.branch 131 (.leaf (1825483980271676:ℤ)) (.branch 147 (.leaf (2025783687680006:ℤ)) (.leaf (2227498096597093:ℤ)))) (.branch 186 (.branch 172 (.leaf (2455286488727365:ℤ)) (.leaf (2596505135941986:ℤ))) (.branch 200 (.leaf (2837537388428299:ℤ)) (.leaf (3108172438508295:ℤ))))), (.branch 163 (.branch 131 (.leaf (1832972657086653:ℤ)) (.branch 147 (.leaf (2037285898146776:ℤ)) (.leaf (2243862963020168:ℤ)))) (.branch 186 (.branch 172 (.leaf (2478101450215661:ℤ)) (.leaf (2623814805640798:ℤ))) (.branch 200 (.leaf (2873368588878959:ℤ)) (.leaf (3154808135273336:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 14 9) 8000 (endpointMeanRuns 14 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 14 9, EndpointRunConditions (endpointMeanCutoff 14 9) (endpointMeanBox 14 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 14 9 h) (endpointMeanCornerA 14 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 9, endpointJoint24Q (endpointMeanCornerK 14 9 h) (endpointMeanCornerA 14 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 14 9, endpointRunWeightQ (endpointMeanCutoff 14 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 14 9) = (449198363/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 14 9 h = (logRoundedQ ((endpointMeanCutoff 14 9:ℚ)/200)).2+(449198363/1000000000000000:ℚ)+((endpointMeanRuns 14 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 14 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 14 9) r*endpointJoint24Q (endpointMeanCornerK 14 9 h) (endpointMeanCornerA 14 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 14 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 14 9 h≤endpointMeanCorner 14 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 14 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint14_09

namespace EndpointAnalyticJoint14_10
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1061 (.leaf (116604700300000:ℤ)) (.branch 1234 (.leaf (8094110700000:ℤ)) (.leaf (7618965000000:ℤ)))) (.branch 2257 (.branch 1684 (.leaf (3843658200000:ℤ)) (.leaf (5866017700000:ℤ))) (.branch 3422 (.leaf (2477099400000:ℤ)) (.leaf (346395100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 131 (.leaf (1830114470926219:ℤ)) (.branch 147 (.leaf (2032673752420224:ℤ)) (.leaf (2236999946248671:ℤ)))) (.branch 186 (.branch 172 (.leaf (2468084272705438:ℤ)) (.leaf (2611504772772683:ℤ))) (.branch 200 (.leaf (2856530636921279:ℤ)) (.leaf (3131938580614946:ℤ))))), (.branch 163 (.branch 131 (.leaf (1837335398504564:ℤ)) (.branch 147 (.leaf (2043751828648950:ℤ)) (.leaf (2252744440658336:ℤ)))) (.branch 186 (.branch 172 (.leaf (2490009378099185:ℤ)) (.leaf (2637731470134445:ℤ))) (.branch 200 (.leaf (2890902123591843:ℤ)) (.leaf (3176618875436031:ℤ))))), (.branch 163 (.branch 131 (.leaf (1832972657086653:ℤ)) (.branch 147 (.leaf (2037285898146776:ℤ)) (.leaf (2243862963020168:ℤ)))) (.branch 186 (.branch 172 (.leaf (2478101450215661:ℤ)) (.leaf (2623814805640798:ℤ))) (.branch 200 (.leaf (2873368588878959:ℤ)) (.leaf (3154808135273336:ℤ))))), (.branch 163 (.branch 131 (.leaf (1840492054675434:ℤ)) (.branch 147 (.leaf (2048853417089679:ℤ)) (.leaf (2260348057987301:ℤ)))) (.branch 186 (.branch 172 (.leaf (2501128412409411:ℤ)) (.leaf (2651411714540008:ℤ))) (.branch 200 (.leaf (2909652250301922:ℤ)) (.leaf (3202143564197969:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 14 10) 8000 (endpointMeanRuns 14 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 14 10, EndpointRunConditions (endpointMeanCutoff 14 10) (endpointMeanBox 14 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 14 10 h) (endpointMeanCornerA 14 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 10, endpointJoint24Q (endpointMeanCornerK 14 10 h) (endpointMeanCornerA 14 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 14 10, endpointRunWeightQ (endpointMeanCutoff 14 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 14 10) = (223858077/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 14 10 h = (logRoundedQ ((endpointMeanCutoff 14 10:ℚ)/200)).2+(223858077/500000000000000:ℚ)+((endpointMeanRuns 14 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 14 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 14 10) r*endpointJoint24Q (endpointMeanCornerK 14 10 h) (endpointMeanCornerA 14 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 14 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 14 10 h≤endpointMeanCorner 14 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 14 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint14_10

namespace EndpointAnalyticJoint14_11
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1141 (.branch 1061 (.leaf (113285596200000:ℤ)) (.leaf (3667739800000:ℤ))) (.branch 1234 (.leaf (3604042800000:ℤ)) (.branch 1343 (.leaf (3455729400000:ℤ)) (.leaf (3253398700000:ℤ))))) (.branch 1929 (.branch 1684 (.leaf (3825157500000:ℤ)) (.leaf (2706930300000:ℤ))) (.branch 2257 (.leaf (1969272400000:ℤ)) (.branch 3422 (.leaf (2467308200000:ℤ)) (.leaf (345203000000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 172 (.branch 147 (.branch 131 (.leaf (1837335398504564:ℤ)) (.leaf (2043751828648950:ℤ))) (.branch 155 (.leaf (2252744440658336:ℤ)) (.branch 163 (.leaf (2367553358893417:ℤ)) (.leaf (2490009378099185:ℤ))))) (.branch 186 (.branch 179 (.leaf (2637731470134445:ℤ)) (.leaf (2760553504181699:ℤ))) (.branch 193 (.leaf (2890902123591843:ℤ)) (.branch 200 (.leaf (3029372530120226:ℤ)) (.leaf (3176618875436031:ℤ)))))), (.branch 172 (.branch 147 (.branch 131 (.leaf (1844584817084933:ℤ)) (.leaf (2054890280416429:ℤ))) (.branch 155 (.leaf (2268599748259853:ℤ)) (.branch 163 (.leaf (2386321794699451:ℤ)) (.leaf (2512129254089644:ℤ))))) (.branch 186 (.branch 179 (.leaf (2664221555739527:ℤ)) (.leaf (2790942900604994:ℤ))) (.branch 193 (.leaf (2925687188566336:ℤ)) (.branch 200 (.leaf (3069110657767492:ℤ)) (.leaf (3221936580185163:ℤ)))))), (.branch 172 (.branch 147 (.branch 131 (.leaf (1840492054675434:ℤ)) (.leaf (2048853417089679:ℤ))) (.branch 155 (.leaf (2260348057987301:ℤ)) (.branch 163 (.leaf (2376766982094008:ℤ)) (.leaf (2501128412409411:ℤ))))) (.branch 186 (.branch 179 (.leaf (2651411714540008:ℤ)) (.leaf (2776585073752681:ℤ))) (.branch 193 (.leaf (2909652250301922:ℤ)) (.branch 200 (.leaf (3051265071276375:ℤ)) (.leaf (3202143564197969:ℤ)))))), (.branch 172 (.branch 147 (.branch 131 (.leaf (1848042299063743:ℤ)) (.leaf (2060486615324143:ℤ))) (.branch 155 (.leaf (2276954264787270:ℤ)) (.branch 163 (.leaf (2396454489605529:ℤ)) (.leaf (2524369345257127:ℤ))))) (.branch 186 (.branch 179 (.leaf (2679298883780436:ℤ)) (.leaf (2808629071314878:ℤ))) (.branch 193 (.leaf (2946394086179553:ℤ)) (.branch 200 (.leaf (3093314645623040:ℤ)) (.leaf (3250189224216029:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 14 11) 8000 (endpointMeanRuns 14 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 14 11, EndpointRunConditions (endpointMeanCutoff 14 11) (endpointMeanBox 14 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 14 11 h) (endpointMeanCornerA 14 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 11, endpointJoint24Q (endpointMeanCornerK 14 11 h) (endpointMeanCornerA 14 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 14 11, endpointRunWeightQ (endpointMeanCutoff 14 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 14 11) = (223247697/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 14 11 h = (logRoundedQ ((endpointMeanCutoff 14 11:ℚ)/200)).2+(223247697/500000000000000:ℚ)+((endpointMeanRuns 14 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 14 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 14 11) r*endpointJoint24Q (endpointMeanCornerK 14 11 h) (endpointMeanCornerA 14 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 14 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 14 11 h≤endpointMeanCorner 14 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 14 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint14_11

namespace EndpointAnalyticJoint14_12
private noncomputable def weights : IntegerLookupTree := (.branch 1583 (.branch 1294 (.branch 1141 (.branch 1061 (.leaf (109425260200000:ℤ)) (.leaf (3642657200000:ℤ))) (.branch 1234 (.leaf (3580363500000:ℤ)) (.leaf (1889673200000:ℤ)))) (.branch 1415 (.branch 1343 (.leaf (1356751700000:ℤ)) (.leaf (1787573400000:ℤ))) (.branch 1474 (.leaf (1251833100000:ℤ)) (.leaf (2013231600000:ℤ))))) (.branch 2080 (.branch 1798 (.branch 1684 (.leaf (1458626000000:ℤ)) (.leaf (1302309400000:ℤ))) (.branch 1929 (.leaf (1143090700000:ℤ)) (.leaf (963548600000:ℤ)))) (.branch 2720 (.branch 2257 (.leaf (782729300000:ℤ)) (.leaf (1187425700000:ℤ))) (.branch 3422 (.leaf (524413200000:ℤ)) (.leaf (343789100000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 167 (.branch 151 (.branch 139 (.branch 131 (.leaf (1844584817084933:ℤ)) (.leaf (2054890280416429:ℤ))) (.branch 147 (.leaf (2158317218144818:ℤ)) (.leaf (2268599748259853:ℤ)))) (.branch 159 (.branch 155 (.leaf (2326492003833485:ℤ)) (.leaf (2386321794699451:ℤ))) (.branch 163 (.leaf (2448171848299184:ℤ)) (.leaf (2512129254089644:ℤ))))) (.branch 182 (.branch 175 (.branch 172 (.leaf (2578285739514997:ℤ)) (.leaf (2664221555739527:ℤ))) (.branch 179 (.leaf (2717587849859989:ℤ)) (.leaf (2790942900604994:ℤ)))) (.branch 193 (.branch 186 (.leaf (2847671232207258:ℤ)) (.leaf (2925687188566336:ℤ))) (.branch 200 (.leaf (3069110657767492:ℤ)) (.leaf (3221936580185163:ℤ)))))), (.branch 167 (.branch 151 (.branch 139 (.branch 131 (.leaf (1851862839081854:ℤ)) (.leaf (2066089436769487:ℤ))) (.branch 147 (.leaf (2171727477479276:ℤ)) (.leaf (2284566648980678:ℤ)))) (.branch 159 (.branch 155 (.leaf (2343881583790394:ℤ)) (.leaf (2405239014557721:ℤ))) (.branch 163 (.leaf (2468728790546622:ℤ)) (.leaf (2534445630911839:ℤ))))) (.branch 182 (.branch 175 (.branch 172 (.leaf (2602489440488128:ℤ)) (.leaf (2690977674730985:ℤ))) (.branch 179 (.leaf (2745985579453129:ℤ)) (.leaf (2821666836972392:ℤ)))) (.branch 193 (.branch 186 (.leaf (2880248795721062:ℤ)) (.leaf (2960890808266502:ℤ))) (.branch 200 (.leaf (3109370054678678:ℤ)) (.leaf (3267900788164377:ℤ)))))), (.branch 167 (.branch 151 (.branch 139 (.branch 131 (.leaf (1848042299063743:ℤ)) (.leaf (2060486615324143:ℤ))) (.branch 147 (.leaf (2165173525828314:ℤ)) (.leaf (2276954264787270:ℤ)))) (.branch 159 (.branch 155 (.leaf (2335697727200765:ℤ)) (.leaf (2396454489605529:ℤ))) (.branch 163 (.leaf (2459313679601449:ℤ)) (.leaf (2524369345257127:ℤ))))) (.branch 182 (.branch 175 (.branch 172 (.leaf (2591720783444751:ℤ)) (.leaf (2679298883780436:ℤ))) (.branch 179 (.leaf (2733736562097788:ℤ)) (.leaf (2808629071314878:ℤ)))) (.branch 193 (.branch 186 (.leaf (2866598030672958:ℤ)) (.leaf (2946394086179553:ℤ))) (.branch 200 (.leaf (3093314645623040:ℤ)) (.leaf (3250189224216029:ℤ)))))), (.branch 167 (.branch 151 (.branch 139 (.branch 131 (.leaf (1855623516794306:ℤ)) (.leaf (2072185865771044:ℤ))) (.branch 147 (.leaf (2179202282704413:ℤ)) (.leaf (2293682473198139:ℤ)))) (.branch 159 (.branch 155 (.leaf (2353930648420242:ℤ)) (.leaf (2416305074926081:ℤ))) (.branch 163 (.leaf (2480902765377601:ℤ)) (.leaf (2547826237012402:ℤ))))) (.branch 182 (.branch 175 (.branch 172 (.leaf (2617183887934575:ℤ)) (.leaf (2707479366278851:ℤ))) (.branch 179 (.leaf (2763667196630539:ℤ)) (.leaf (2841042882065753:ℤ)))) (.branch 193 (.branch 186 (.leaf (2900993126581715:ℤ)) (.leaf (2983599882141594:ℤ))) (.branch 200 (.leaf (3135943706399580:ℤ)) (.leaf (3298955771789655:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 14 12) 8000 (endpointMeanRuns 14 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 14 12, EndpointRunConditions (endpointMeanCutoff 14 12) (endpointMeanBox 14 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 14 12 h) (endpointMeanCornerA 14 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 12, endpointJoint24Q (endpointMeanCornerK 14 12 h) (endpointMeanCornerA 14 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 14 12, endpointRunWeightQ (endpointMeanCutoff 14 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 14 12) = (445047367/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 14 12 h = (logRoundedQ ((endpointMeanCutoff 14 12:ℚ)/200)).2+(445047367/1000000000000000:ℚ)+((endpointMeanRuns 14 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 14 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 14 12) r*endpointJoint24Q (endpointMeanCornerK 14 12 h) (endpointMeanCornerA 14 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 14 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 14 12 h≤endpointMeanCorner 14 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 14 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint14_12

namespace EndpointAnalyticJoint14_13
private noncomputable def weights : IntegerLookupTree := (.branch 1516 (.branch 1234 (.branch 1141 (.branch 1061 (.leaf (106307234000000:ℤ)) (.branch 1094 (.leaf (1479035400000:ℤ)) (.leaf (1975010400000:ℤ)))) (.branch 1179 (.leaf (1446936700000:ℤ)) (.branch 1206 (.leaf (948426000000:ℤ)) (.leaf (929682200000:ℤ))))) (.branch 1343 (.branch 1263 (.leaf (908473600000:ℤ)) (.branch 1294 (.leaf (912826700000:ℤ)) (.leaf (1349753400000:ℤ)))) (.branch 1415 (.branch 1378 (.leaf (867832300000:ℤ)) (.leaf (849721800000:ℤ))) (.branch 1474 (.leaf (1245656100000:ℤ)) (.leaf (780784100000:ℤ)))))) (.branch 2080 (.branch 1684 (.branch 1583 (.leaf (1130241100000:ℤ)) (.branch 1632 (.leaf (714126200000:ℤ)) (.leaf (678006500000:ℤ)))) (.branch 1798 (.leaf (1296403800000:ℤ)) (.branch 1929 (.leaf (1138055900000:ℤ)) (.leaf (959431200000:ℤ))))) (.branch 2720 (.branch 2257 (.leaf (779488500000:ℤ)) (.branch 2467 (.leaf (598046400000:ℤ)) (.leaf (426352900000:ℤ)))) (.branch 3422 (.branch 3031 (.leaf (275831600000:ℤ)) (.leaf (155734600000:ℤ))) (.branch 4612 (.leaf (129779800000:ℤ)) (.leaf (12980100000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 170 (.branch 147 (.branch 135 (.branch 123 (.leaf (1851862839081854:ℤ)) (.branch 131 (.leaf (1967081560962685:ℤ)) (.leaf (2066089436769487:ℤ)))) (.branch 139 (.leaf (2118045347995789:ℤ)) (.branch 143 (.leaf (2171727477479276:ℤ)) (.leaf (2227208937011181:ℤ))))) (.branch 159 (.branch 151 (.leaf (2284566648980678:ℤ)) (.branch 155 (.leaf (2343881583790394:ℤ)) (.leaf (2405239014557721:ℤ)))) (.branch 165 (.branch 163 (.leaf (2468728790546622:ℤ)) (.leaf (2534445630911839:ℤ))) (.branch 167 (.leaf (2568170208813775:ℤ)) (.leaf (2602489440488128:ℤ)))))) (.branch 184 (.branch 177 (.branch 172 (.leaf (2655112576204837:ℤ)) (.branch 175 (.leaf (2690977674730985:ℤ)) (.leaf (2745985579453129:ℤ)))) (.branch 179 (.leaf (2783485934930183:ℤ)) (.branch 182 (.leaf (2821666836972392:ℤ)) (.leaf (2880248795721062:ℤ))))) (.branch 190 (.branch 186 (.leaf (2920200965486448:ℤ)) (.branch 188 (.leaf (2960890808266502:ℤ)) (.leaf (3002335711498091:ℤ)))) (.branch 197 (.branch 193 (.leaf (3044553566126313:ℤ)) (.leaf (3109370054678678:ℤ))) (.branch 200 (.leaf (3198673784721232:ℤ)) (.leaf (3267900788164377:ℤ))))))), (.branch 170 (.branch 147 (.branch 135 (.branch 123 (.leaf (1859169577353408:ℤ)) (.branch 131 (.leaf (1976417170562165:ℤ)) (.leaf (2077349628548237:ℤ)))) (.branch 139 (.leaf (2130381053658933:ℤ)) (.branch 143 (.leaf (2185221058697053:ℤ)) (.leaf (2241948371298040:ℤ))))) (.branch 159 (.branch 151 (.leaf (2300645928237569:ℤ)) (.branch 155 (.leaf (2361401143773274:ℤ)) (.leaf (2424306197932208:ℤ)))) (.branch 165 (.branch 163 (.leaf (2489458346442427:ℤ)) (.leaf (2556960254171261:ℤ))) (.branch 167 (.leaf (2591626017360465:ℤ)) (.leaf (2626920354113380:ℤ)))))) (.branch 184 (.branch 177 (.branch 172 (.leaf (2681072306514384:ℤ)) (.branch 175 (.leaf (2718002498816412:ℤ)) (.leaf (2774680054208010:ℤ)))) (.branch 179 (.leaf (2813343461213384:ℤ)) (.branch 182 (.leaf (2852728996047856:ℤ)) (.leaf (2913199048902301:ℤ))))) (.branch 190 (.branch 186 (.leaf (2954466254001602:ℤ)) (.branch 188 (.leaf (2996518018993359:ℤ)) (.leaf (3039373377220776:ℤ)))) (.branch 197 (.branch 193 (.leaf (3083051927761847:ℤ)) (.leaf (3150157558660731:ℤ))) (.branch 200 (.leaf (3242706443840008:ℤ)) (.leaf (3314520722400949:ℤ))))))), (.branch 170 (.branch 147 (.branch 135 (.branch 123 (.leaf (1855623516794306:ℤ)) (.branch 131 (.leaf (1972022813633735:ℤ)) (.leaf (2072185865771044:ℤ)))) (.branch 139 (.leaf (2124800752600367:ℤ)) (.branch 143 (.leaf (2179202282704413:ℤ)) (.leaf (2235468692584976:ℤ))))) (.branch 159 (.branch 151 (.leaf (2293682473198139:ℤ)) (.branch 155 (.leaf (2353930648420242:ℤ)) (.leaf (2416305074926081:ℤ)))) (.branch 165 (.branch 163 (.leaf (2480902765377601:ℤ)) (.leaf (2547826237012402:ℤ))) (.branch 167 (.leaf (2582193774562250:ℤ)) (.leaf (2617183887934575:ℤ)))))) (.branch 184 (.branch 177 (.branch 172 (.leaf (2670868298200807:ℤ)) (.branch 175 (.leaf (2707479366278851:ℤ)) (.leaf (2763667196630539:ℤ)))) (.branch 179 (.leaf (2801996844183820:ℤ)) (.branch 182 (.leaf (2841042882065753:ℤ)) (.leaf (2900993126581715:ℤ))))) (.branch 190 (.branch 186 (.leaf (2941906906063887:ℤ)) (.branch 188 (.leaf (2983599882141594:ℤ)) (.leaf (3026091233705787:ℤ)))) (.branch 197 (.branch 193 (.leaf (3069400724938986:ℤ)) (.leaf (3135943706399580:ℤ))) (.branch 200 (.leaf (3227726638752682:ℤ)) (.leaf (3298955771789655:ℤ))))))), (.branch 170 (.branch 147 (.branch 135 (.branch 123 (.leaf (1863235834928962:ℤ)) (.branch 131 (.leaf (1981764290443104:ℤ)) (.leaf (2083951543468675:ℤ)))) (.branch 139 (.leaf (2137699372146673:ℤ)) (.branch 143 (.leaf (2193321935768344:ℤ)) (.leaf (2250903635379439:ℤ))))) (.branch 159 (.branch 151 (.leaf (2310533579534966:ℤ)) (.branch 155 (.leaf (2372305899450776:ℤ)) (.leaf (2436320088880378:ℤ)))) (.branch 165 (.branch 163 (.leaf (2502681370948857:ℤ)) (.leaf (2571501094404067:ℤ))) (.branch 167 (.leaf (2606869447826643:ℤ)) (.leaf (2642897162000688:ℤ)))))) (.branch 184 (.branch 177 (.branch 172 (.leaf (2698209808138551:ℤ)) (.branch 175 (.leaf (2735956247062147:ℤ)) (.leaf (2793925530216645:ℤ)))) (.branch 179 (.leaf (2833497263891411:ℤ)) (.branch 182 (.leaf (2873830773943298:ℤ)) (.leaf (2935800914681675:ℤ))))) (.branch 190 (.branch 186 (.leaf (2978122914905386:ℤ)) (.branch 188 (.leaf (3021275496876241:ℤ)) (.leaf (3065279707172327:ℤ)))) (.branch 197 (.branch 193 (.leaf (3110157251483398:ℤ)) (.leaf (3179160239525638:ℤ))) (.branch 200 (.leaf (3274435885942711:ℤ)) (.leaf (3348454023272868:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 14 13) 8000 (endpointMeanRuns 14 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 14 13, EndpointRunConditions (endpointMeanCutoff 14 13) (endpointMeanBox 14 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 14 13 h) (endpointMeanCornerA 14 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 13, endpointJoint24Q (endpointMeanCornerK 14 13 h) (endpointMeanCornerA 14 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 14 13, endpointRunWeightQ (endpointMeanCutoff 14 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 14 13) = (221927219/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 14 13 h = (logRoundedQ ((endpointMeanCutoff 14 13:ℚ)/200)).2+(221927219/500000000000000:ℚ)+((endpointMeanRuns 14 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 14 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 14 13) r*endpointJoint24Q (endpointMeanCornerK 14 13 h) (endpointMeanCornerA 14 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 14 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 14 13 h≤endpointMeanCorner 14 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 14 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint14_13

namespace EndpointAnalyticJoint14_14
private noncomputable def weights : IntegerLookupTree := (.branch 1583 (.branch 1234 (.branch 1117 (.branch 1061 (.leaf (102680329900000:ℤ)) (.branch 1094 (.leaf (1468915600000:ℤ)) (.leaf (955711400000:ℤ)))) (.branch 1179 (.branch 1141 (.leaf (951876500000:ℤ)) (.leaf (1437426700000:ℤ))) (.branch 1206 (.leaf (942284300000:ℤ)) (.leaf (923733300000:ℤ))))) (.branch 1378 (.branch 1294 (.branch 1263 (.leaf (902729400000:ℤ)) (.leaf (907124500000:ℤ))) (.branch 1343 (.leaf (1341450000000:ℤ)) (.leaf (862577200000:ℤ)))) (.branch 1474 (.branch 1415 (.leaf (844641600000:ℤ)) (.leaf (1238327300000:ℤ))) (.branch 1516 (.leaf (776265800000:ℤ)) (.leaf (1123807000000:ℤ)))))) (.branch 2080 (.branch 1798 (.branch 1684 (.branch 1632 (.leaf (710129900000:ℤ)) (.leaf (674264900000:ℤ))) (.branch 1739 (.leaf (633725500000:ℤ)) (.leaf (599125500000:ℤ)))) (.branch 1929 (.branch 1861 (.leaf (558367600000:ℤ)) (.leaf (520300500000:ℤ))) (.branch 2002 (.leaf (476350800000:ℤ)) (.leaf (429075200000:ℤ))))) (.branch 2720 (.branch 2257 (.branch 2165 (.leaf (388594700000:ℤ)) (.leaf (343611100000:ℤ))) (.branch 2467 (.leaf (595192800000:ℤ)) (.leaf (424388700000:ℤ)))) (.branch 3422 (.branch 3031 (.leaf (274607100000:ℤ)) (.leaf (155070100000:ℤ))) (.branch 4612 (.leaf (129253800000:ℤ)) (.leaf (12932100000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 149 (.branch 135 (.branch 123 (.leaf (1859169577353408:ℤ)) (.branch 131 (.leaf (1976417170562165:ℤ)) (.leaf (2077349628548237:ℤ)))) (.branch 143 (.branch 139 (.leaf (2130381053658933:ℤ)) (.leaf (2185221058697053:ℤ))) (.branch 147 (.leaf (2241948371298040:ℤ)) (.leaf (2300645928237569:ℤ))))) (.branch 157 (.branch 153 (.branch 151 (.leaf (2330760682648903:ℤ)) (.leaf (2361401143773274:ℤ))) (.branch 155 (.leaf (2392578985291490:ℤ)) (.leaf (2424306197932208:ℤ)))) (.branch 161 (.branch 159 (.leaf (2456595099692783:ℤ)) (.leaf (2489458346442427:ℤ))) (.branch 163 (.leaf (2522908942923960:ℤ)) (.leaf (2556960254171261:ℤ)))))) (.branch 184 (.branch 175 (.branch 170 (.branch 167 (.leaf (2591626017360465:ℤ)) (.leaf (2626920354113380:ℤ))) (.branch 172 (.leaf (2681072306514384:ℤ)) (.leaf (2718002498816412:ℤ)))) (.branch 179 (.branch 177 (.leaf (2774680054208010:ℤ)) (.leaf (2813343461213384:ℤ))) (.branch 182 (.leaf (2852728996047856:ℤ)) (.leaf (2913199048902301:ℤ))))) (.branch 193 (.branch 188 (.branch 186 (.leaf (2954466254001602:ℤ)) (.leaf (2996518018993359:ℤ))) (.branch 190 (.leaf (3039373377220776:ℤ)) (.leaf (3083051927761847:ℤ)))) (.branch 197 (.branch 195 (.leaf (3150157558660731:ℤ)) (.leaf (3195983731126421:ℤ))) (.branch 200 (.leaf (3242706443840008:ℤ)) (.leaf (3314520722400949:ℤ))))))), (.branch 165 (.branch 149 (.branch 135 (.branch 123 (.leaf (1866505145202961:ℤ)) (.branch 131 (.leaf (1985797086207882:ℤ)) (.leaf (2088671188395880:ℤ)))) (.branch 143 (.branch 139 (.leaf (2142788603692346:ℤ)) (.leaf (2198798479501502:ℤ))) (.branch 147 (.leaf (2256785349609391:ℤ)) (.leaf (2316838376975218:ℤ))))) (.branch 157 (.branch 153 (.branch 151 (.leaf (2347668902605257:ℤ)) (.leaf (2379051655329868:ℤ))) (.branch 155 (.leaf (2410999220524388:ℤ)) (.leaf (2443524533636937:ℤ)))) (.branch 161 (.branch 159 (.leaf (2476640891719403:ℤ)) (.leaf (2510361965398246:ℤ))) (.branch 163 (.leaf (2544701811304137:ℤ)) (.leaf (2579674884980395:ℤ)))))) (.branch 184 (.branch 175 (.branch 170 (.branch 167 (.leaf (2615296054291514:ℤ)) (.leaf (2651580613353369:ℤ))) (.branch 172 (.leaf (2707285851898956:ℤ)) (.leaf (2745298726534690:ℤ)))) (.branch 179 (.branch 177 (.leaf (2803674374995446:ℤ)) (.leaf (2843521259233746:ℤ))) (.branch 182 (.leaf (2884133101136853:ℤ)) (.leaf (2946526255347551:ℤ))))) (.branch 193 (.branch 188 (.branch 186 (.leaf (2989133607309867:ℤ)) (.leaf (3032573917647730:ℤ))) (.branch 190 (.leaf (3076867950103087:ℤ)) (.leaf (3122037100950025:ℤ)))) (.branch 197 (.branch 195 (.leaf (3191480097216297:ℤ)) (.leaf (3238935012413824:ℤ))) (.branch 200 (.leaf (3287345252631918:ℤ)) (.leaf (3361805737498022:ℤ))))))), (.branch 165 (.branch 149 (.branch 135 (.branch 123 (.leaf (1863235834928962:ℤ)) (.branch 131 (.leaf (1981764290443104:ℤ)) (.leaf (2083951543468675:ℤ)))) (.branch 143 (.branch 139 (.leaf (2137699372146673:ℤ)) (.leaf (2193321935768344:ℤ))) (.branch 147 (.leaf (2250903635379439:ℤ)) (.leaf (2310533579534966:ℤ))))) (.branch 157 (.branch 153 (.branch 151 (.leaf (2341145854009185:ℤ)) (.leaf (2372305899450776:ℤ))) (.branch 155 (.leaf (2404026322806768:ℤ)) (.leaf (2436320088880378:ℤ)))) (.branch 161 (.branch 159 (.leaf (2469200532463529:ℤ)) (.leaf (2502681370948857:ℤ))) (.branch 163 (.leaf (2536776717443030:ℤ)) (.leaf (2571501094404067:ℤ)))))) (.branch 184 (.branch 175 (.branch 170 (.branch 167 (.leaf (2606869447826643:ℤ)) (.leaf (2642897162000688:ℤ))) (.branch 172 (.leaf (2698209808138551:ℤ)) (.leaf (2735956247062147:ℤ)))) (.branch 179 (.branch 177 (.leaf (2793925530216645:ℤ)) (.leaf (2833497263891411:ℤ))) (.branch 182 (.leaf (2873830773943298:ℤ)) (.leaf (2935800914681675:ℤ))))) (.branch 193 (.branch 188 (.branch 186 (.leaf (2978122914905386:ℤ)) (.leaf (3021275496876241:ℤ))) (.branch 190 (.leaf (3065279707172327:ℤ)) (.leaf (3110157251483398:ℤ)))) (.branch 197 (.branch 195 (.leaf (3179160239525638:ℤ)) (.leaf (3226320632373399:ℤ))) (.branch 200 (.leaf (3274435885942711:ℤ)) (.leaf (3348454023272868:ℤ))))))), (.branch 165 (.branch 149 (.branch 135 (.branch 123 (.leaf (1870879381050788:ℤ)) (.branch 131 (.leaf (1991553888587464:ℤ)) (.leaf (2095784025584759:ℤ)))) (.branch 143 (.branch 139 (.leaf (2150676292863568:ℤ)) (.leaf (2207533073961593:ℤ))) (.branch 147 (.leaf (2266445149766635:ℤ)) (.leaf (2327508486697804:ℤ))))) (.branch 157 (.branch 153 (.branch 151 (.leaf (2358878372214945:ℤ)) (.leaf (2390824591347196:ℤ))) (.branch 155 (.leaf (2423360760899048:ℤ)) (.leaf (2456500893482454:ℤ)))) (.branch 161 (.branch 159 (.leaf (2490259411222454:ℤ)) (.leaf (2524651160014785:ℤ))) (.branch 163 (.leaf (2559691424361019:ℤ)) (.leaf (2595395942807828:ℤ)))))) (.branch 184 (.branch 175 (.branch 170 (.branch 167 (.leaf (2631780924018397:ℤ)) (.leaf (2668863063505883:ℤ))) (.branch 172 (.leaf (2725831211385207:ℤ)) (.leaf (2764732643605099:ℤ)))) (.branch 179 (.branch 177 (.leaf (2824515150707532:ℤ)) (.leaf (2865351815490271:ℤ))) (.branch 182 (.leaf (2906997064140897:ℤ)) (.leaf (2971026346691681:ℤ))))) (.branch 193 (.branch 188 (.branch 186 (.leaf (3014784756785885:ℤ)) (.leaf (3059426863052665:ℤ))) (.branch 190 (.leaf (3104975679036643:ℤ)) (.leaf (3151454956780542:ℤ)))) (.branch 197 (.branch 195 (.leaf (3222972340975084:ℤ)) (.leaf (3271886793137776:ℤ))) (.branch 200 (.leaf (3321821074442900:ℤ)) (.leaf (3398694957310621:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 14 14) 8000 (endpointMeanRuns 14 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 14 14, EndpointRunConditions (endpointMeanCutoff 14 14) (endpointMeanBox 14 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 14 14 h) (endpointMeanCornerA 14 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 14, endpointJoint24Q (endpointMeanCornerK 14 14 h) (endpointMeanCornerA 14 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 14 14, endpointRunWeightQ (endpointMeanCutoff 14 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 14 14) = (442439053/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 14 14 h = (logRoundedQ ((endpointMeanCutoff 14 14:ℚ)/200)).2+(442439053/1000000000000000:ℚ)+((endpointMeanRuns 14 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 14 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 14 14) r*endpointJoint24Q (endpointMeanCornerK 14 14 h) (endpointMeanCornerA 14 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 14 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 14 14 h≤endpointMeanCorner 14 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 14 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint14_14

namespace EndpointAnalyticJoint14_15
private noncomputable def weights : IntegerLookupTree := (.branch 1583 (.branch 1234 (.branch 1117 (.branch 1061 (.leaf (99174407500000:ℤ)) (.branch 1094 (.leaf (1458918700000:ℤ)) (.leaf (949300500000:ℤ)))) (.branch 1179 (.branch 1141 (.leaf (945564600000:ℤ)) (.leaf (1428032200000:ℤ))) (.branch 1206 (.leaf (936217100000:ℤ)) (.leaf (917856600000:ℤ))))) (.branch 1378 (.branch 1294 (.branch 1263 (.leaf (897055000000:ℤ)) (.leaf (901491600000:ℤ))) (.branch 1343 (.leaf (1333247500000:ℤ)) (.leaf (857385800000:ℤ)))) (.branch 1474 (.branch 1415 (.leaf (839623200000:ℤ)) (.leaf (1231087500000:ℤ))) (.branch 1516 (.leaf (771802300000:ℤ)) (.leaf (1117451000000:ℤ)))))) (.branch 2002 (.branch 1739 (.branch 1632 (.leaf (706182200000:ℤ)) (.branch 1684 (.leaf (670568900000:ℤ)) (.leaf (630300700000:ℤ)))) (.branch 1861 (.branch 1798 (.leaf (595934100000:ℤ)) (.leaf (555436900000:ℤ))) (.branch 1929 (.leaf (517610400000:ℤ)) (.leaf (473925500000:ℤ))))) (.branch 2720 (.branch 2257 (.branch 2080 (.leaf (426924600000:ℤ)) (.leaf (771845000000:ℤ))) (.branch 2467 (.leaf (592374000000:ℤ)) (.leaf (422448300000:ℤ)))) (.branch 3422 (.branch 3031 (.leaf (273397500000:ℤ)) (.leaf (154413700000:ℤ))) (.branch 4612 (.leaf (128734200000:ℤ)) (.leaf (12884700000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 167 (.branch 151 (.branch 135 (.branch 123 (.leaf (1866505145202961:ℤ)) (.branch 131 (.leaf (1985797086207882:ℤ)) (.leaf (2088671188395880:ℤ)))) (.branch 143 (.branch 139 (.leaf (2142788603692346:ℤ)) (.leaf (2198798479501502:ℤ))) (.branch 147 (.leaf (2256785349609391:ℤ)) (.leaf (2316838376975218:ℤ))))) (.branch 159 (.branch 155 (.branch 153 (.leaf (2379051655329868:ℤ)) (.leaf (2410999220524388:ℤ))) (.branch 157 (.leaf (2443524533636937:ℤ)) (.leaf (2476640891719403:ℤ)))) (.branch 163 (.branch 161 (.leaf (2510361965398246:ℤ)) (.leaf (2544701811304137:ℤ))) (.branch 165 (.leaf (2579674884980395:ℤ)) (.leaf (2615296054291514:ℤ)))))) (.branch 184 (.branch 175 (.branch 170 (.leaf (2651580613353369:ℤ)) (.branch 172 (.leaf (2707285851898956:ℤ)) (.leaf (2745298726534690:ℤ)))) (.branch 179 (.branch 177 (.leaf (2803674374995446:ℤ)) (.leaf (2843521259233746:ℤ))) (.branch 182 (.leaf (2884133101136853:ℤ)) (.leaf (2946526255347551:ℤ))))) (.branch 193 (.branch 188 (.branch 186 (.leaf (2989133607309867:ℤ)) (.leaf (3032573917647730:ℤ))) (.branch 190 (.leaf (3076867950103087:ℤ)) (.leaf (3122037100950025:ℤ)))) (.branch 197 (.branch 195 (.leaf (3191480097216297:ℤ)) (.leaf (3238935012413824:ℤ))) (.branch 200 (.leaf (3287345252631918:ℤ)) (.leaf (3361805737498022:ℤ))))))), (.branch 167 (.branch 151 (.branch 135 (.branch 123 (.leaf (1873869656380942:ℤ)) (.branch 131 (.leaf (1995221518172746:ℤ)) (.leaf (2100054450768524:ℤ)))) (.branch 143 (.branch 139 (.leaf (2155268416524733:ℤ)) (.leaf (2212460260812625:ℤ))) (.branch 147 (.leaf (2271720517481316:ℤ)) (.leaf (2333144791705155:ℤ))))) (.branch 159 (.branch 155 (.branch 153 (.leaf (2396834097269840:ℤ)) (.leaf (2429561271374713:ℤ))) (.branch 157 (.leaf (2462895219910079:ℤ)) (.leaf (2496850257213225:ℤ)))) (.branch 163 (.branch 161 (.leaf (2531441108996238:ℤ)) (.leaf (2566682926316667:ℤ))) (.branch 165 (.leaf (2602591300096477:ℤ)) (.leaf (2639182276213971:ℤ)))))) (.branch 184 (.branch 175 (.branch 170 (.leaf (2676472371193925:ℤ)) (.branch 172 (.leaf (2733755693974957:ℤ)) (.leaf (2772869083525468:ℤ)))) (.branch 179 (.branch 177 (.leaf (2832971675089140:ℤ)) (.leaf (2874022764439501:ℤ))) (.branch 182 (.leaf (2915882916532654:ℤ)) (.leaf (2980234727429239:ℤ))))) (.branch 193 (.branch 188 (.branch 186 (.leaf (3024207743191381:ℤ)) (.leaf (3069063662459383:ℤ))) (.branch 190 (.leaf (3114825066681468:ℤ)) (.leaf (3161515241420010:ℤ)))) (.branch 197 (.branch 195 (.leaf (3233344688720283:ℤ)) (.leaf (3282463522097685:ℤ))) (.branch 200 (.leaf (3332598555299505:ℤ)) (.leaf (3409765321511683:ℤ))))))), (.branch 167 (.branch 151 (.branch 135 (.branch 123 (.leaf (1870879381050788:ℤ)) (.branch 131 (.leaf (1991553888587464:ℤ)) (.leaf (2095784025584759:ℤ)))) (.branch 143 (.branch 139 (.leaf (2150676292863568:ℤ)) (.leaf (2207533073961593:ℤ))) (.branch 147 (.leaf (2266445149766635:ℤ)) (.leaf (2327508486697804:ℤ))))) (.branch 159 (.branch 155 (.branch 153 (.leaf (2390824591347196:ℤ)) (.leaf (2423360760899048:ℤ))) (.branch 157 (.leaf (2456500893482454:ℤ)) (.leaf (2490259411222454:ℤ)))) (.branch 163 (.branch 161 (.leaf (2524651160014785:ℤ)) (.leaf (2559691424361019:ℤ))) (.branch 165 (.leaf (2595395942807828:ℤ)) (.leaf (2631780924018397:ℤ)))))) (.branch 184 (.branch 175 (.branch 170 (.leaf (2668863063505883:ℤ)) (.branch 172 (.leaf (2725831211385207:ℤ)) (.leaf (2764732643605099:ℤ)))) (.branch 179 (.branch 177 (.leaf (2824515150707532:ℤ)) (.leaf (2865351815490271:ℤ))) (.branch 182 (.leaf (2906997064140897:ℤ)) (.leaf (2971026346691681:ℤ))))) (.branch 193 (.branch 188 (.branch 186 (.leaf (3014784756785885:ℤ)) (.leaf (3059426863052665:ℤ))) (.branch 190 (.leaf (3104975679036643:ℤ)) (.leaf (3151454956780542:ℤ)))) (.branch 197 (.branch 195 (.leaf (3222972340975084:ℤ)) (.leaf (3271886793137776:ℤ))) (.branch 200 (.leaf (3321821074442900:ℤ)) (.leaf (3398694957310621:ℤ))))))), (.branch 167 (.branch 151 (.branch 135 (.branch 123 (.leaf (1878554283266262:ℤ)) (.branch 131 (.leaf (2001391845778501:ℤ)) (.leaf (2107683691428535:ℤ)))) (.branch 143 (.branch 139 (.leaf (2163731990078924:ℤ)) (.leaf (2221836290041565:ℤ))) (.branch 147 (.leaf (2282093971577236:ℤ)) (.leaf (2344608104220068:ℤ))))) (.branch 159 (.branch 155 (.branch 153 (.leaf (2409487843837431:ℤ)) (.leaf (2442850696663203:ℤ))) (.branch 157 (.leaf (2476848862028316:ℤ)) (.leaf (2511497893204667:ℤ)))) (.branch 163 (.branch 161 (.leaf (2546813810879738:ℤ)) (.leaf (2582813119852162:ℤ))) (.branch 165 (.leaf (2619512826419536:ℤ)) (.leaf (2656930456491248:ℤ)))))) (.branch 184 (.branch 175 (.branch 170 (.leaf (2695084074460915:ℤ)) (.branch 172 (.leaf (2753735373190896:ℤ)) (.leaf (2793811706171640:ℤ)))) (.branch 179 (.branch 177 (.leaf (2855439685236627:ℤ)) (.leaf (2897564480178031:ℤ))) (.branch 182 (.leaf (2940546119675774:ℤ)) (.leaf (3006674433744168:ℤ))))) (.branch 193 (.branch 188 (.branch 186 (.leaf (3051897920082083:ℤ)) (.leaf (3098059988255251:ℤ))) (.branch 190 (.leaf (3145185721502273:ℤ)) (.leaf (3193301026782398:ℤ)))) (.branch 197 (.branch 195 (.leaf (3267388218292614:ℤ)) (.leaf (3318096496576109:ℤ))) (.branch 200 (.leaf (3369891985970638:ℤ)) (.leaf (3449689717273837:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 14 15) 8000 (endpointMeanRuns 14 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 14 15, EndpointRunConditions (endpointMeanCutoff 14 15) (endpointMeanBox 14 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 14 15 h) (endpointMeanCornerA 14 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 15, endpointJoint24Q (endpointMeanCornerK 14 15 h) (endpointMeanCornerA 14 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 14 15, endpointRunWeightQ (endpointMeanCutoff 14 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 14 15) = (220520429/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 14 15 h = (logRoundedQ ((endpointMeanCutoff 14 15:ℚ)/200)).2+(220520429/500000000000000:ℚ)+((endpointMeanRuns 14 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 14 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 14 15) r*endpointJoint24Q (endpointMeanCornerK 14 15 h) (endpointMeanCornerA 14 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 14 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 14 15 h≤endpointMeanCorner 14 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 14 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint14_15

namespace EndpointAnalyticJoint14_16
private noncomputable def weights : IntegerLookupTree := (.branch 1583 (.branch 1234 (.branch 1094 (.branch 1061 (.leaf (96342146900000:ℤ)) (.leaf (1450679700000:ℤ))) (.branch 1141 (.leaf (1937890300000:ℤ)) (.branch 1179 (.leaf (1420289700000:ℤ)) (.leaf (1901326600000:ℤ))))) (.branch 1343 (.branch 1294 (.leaf (1846606200000:ℤ)) (.leaf (1326487400000:ℤ))) (.branch 1415 (.leaf (1748556100000:ℤ)) (.branch 1474 (.leaf (1225120700000:ℤ)) (.leaf (1971360000000:ℤ)))))) (.branch 2257 (.branch 1798 (.branch 1684 (.leaf (1429205600000:ℤ)) (.leaf (1276770600000:ℤ))) (.branch 1929 (.leaf (1121317500000:ℤ)) (.branch 2080 (.leaf (945742800000:ℤ)) (.leaf (768714500000:ℤ))))) (.branch 2720 (.branch 2467 (.leaf (590050800000:ℤ)) (.leaf (420849100000:ℤ))) (.branch 3422 (.leaf (516057700000:ℤ)) (.branch 4612 (.leaf (128306000000:ℤ)) (.leaf (12845600000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 167 (.branch 147 (.branch 131 (.branch 123 (.leaf (1873869656380942:ℤ)) (.leaf (1995221518172746:ℤ))) (.branch 139 (.leaf (2100054450768524:ℤ)) (.branch 143 (.leaf (2212460260812625:ℤ)) (.leaf (2271720517481316:ℤ))))) (.branch 155 (.branch 151 (.leaf (2333144791705155:ℤ)) (.leaf (2396834097269840:ℤ))) (.branch 159 (.leaf (2462895219910079:ℤ)) (.branch 163 (.leaf (2531441108996238:ℤ)) (.leaf (2602591300096477:ℤ)))))) (.branch 186 (.branch 175 (.branch 172 (.leaf (2676472371193925:ℤ)) (.leaf (2772869083525468:ℤ))) (.branch 179 (.leaf (2832971675089140:ℤ)) (.branch 182 (.leaf (2915882916532654:ℤ)) (.leaf (2980234727429239:ℤ))))) (.branch 193 (.branch 190 (.leaf (3069063662459383:ℤ)) (.leaf (3161515241420010:ℤ))) (.branch 197 (.leaf (3233344688720283:ℤ)) (.branch 200 (.leaf (3332598555299505:ℤ)) (.leaf (3409765321511683:ℤ))))))), (.branch 167 (.branch 147 (.branch 131 (.branch 123 (.leaf (1881263225086586:ℤ)) (.leaf (2004690677727587:ℤ))) (.branch 139 (.leaf (2111499751945053:ℤ)) (.branch 143 (.leaf (2226206926787042:ℤ)) (.leaf (2286754524721995:ℤ))))) (.branch 155 (.branch 151 (.leaf (2349565974544940:ℤ)) (.leaf (2414749455719058:ℤ))) (.branch 159 (.leaf (2482419464488660:ℤ)) (.branch 163 (.leaf (2552697251091239:ℤ)) (.leaf (2625711292060494:ℤ)))))) (.branch 186 (.branch 175 (.branch 172 (.leaf (2701597800832074:ℤ)) (.leaf (2800716322801313:ℤ))) (.branch 179 (.leaf (2862575120504292:ℤ)) (.branch 182 (.leaf (2947982247967528:ℤ)) (.leaf (3014328826853636:ℤ))))) (.branch 193 (.branch 190 (.leaf (3105992473725004:ℤ)) (.leaf (3201492582740143:ℤ))) (.branch 197 (.leaf (3275758443611922:ℤ)) (.branch 200 (.leaf (3378474810910870:ℤ)) (.leaf (3458409097854814:ℤ))))))), (.branch 167 (.branch 147 (.branch 131 (.branch 123 (.leaf (1878554283266262:ℤ)) (.leaf (2001391845778501:ℤ))) (.branch 139 (.leaf (2107683691428535:ℤ)) (.branch 143 (.leaf (2221836290041565:ℤ)) (.leaf (2282093971577236:ℤ))))) (.branch 155 (.branch 151 (.leaf (2344608104220068:ℤ)) (.leaf (2409487843837431:ℤ))) (.branch 159 (.leaf (2476848862028316:ℤ)) (.branch 163 (.leaf (2546813810879738:ℤ)) (.leaf (2619512826419536:ℤ)))))) (.branch 186 (.branch 175 (.branch 172 (.leaf (2695084074460915:ℤ)) (.leaf (2793811706171640:ℤ))) (.branch 179 (.leaf (2855439685236627:ℤ)) (.branch 182 (.leaf (2940546119675774:ℤ)) (.leaf (3006674433744168:ℤ))))) (.branch 193 (.branch 190 (.leaf (3098059988255251:ℤ)) (.leaf (3193301026782398:ℤ))) (.branch 197 (.leaf (3267388218292614:ℤ)) (.branch 200 (.leaf (3369891985970638:ℤ)) (.leaf (3449689717273837:ℤ))))))), (.branch 167 (.branch 147 (.branch 131 (.branch 123 (.leaf (1886260670207368:ℤ)) (.leaf (2011278400902160:ℤ))) (.branch 139 (.leaf (2119650922462936:ℤ)) (.branch 143 (.leaf (2236232180606297:ℤ)) (.leaf (2297850841722512:ℤ))))) (.branch 155 (.branch 151 (.leaf (2361833348317312:ℤ)) (.leaf (2428296785390254:ℤ))) (.branch 159 (.leaf (2497365379189422:ℤ)) (.branch 163 (.leaf (2569171016581083:ℤ)) (.leaf (2643853808430085:ℤ)))))) (.branch 186 (.branch 175 (.branch 172 (.leaf (2721562701261771:ℤ)) (.leaf (2823196618159710:ℤ))) (.branch 179 (.leaf (2886702800649449:ℤ)) (.branch 182 (.leaf (2974482357964006:ℤ)) (.leaf (3042750247098007:ℤ))))) (.branch 193 (.branch 190 (.leaf (3137180955929555:ℤ)) (.leaf (3235702742858405:ℤ))) (.branch 197 (.leaf (3312416192131368:ℤ)) (.branch 200 (.leaf (3418658543796993:ℤ)) (.leaf (3501449613731027:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 14 16) 8000 (endpointMeanRuns 14 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 14 16, EndpointRunConditions (endpointMeanCutoff 14 16) (endpointMeanBox 14 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 14 16 h) (endpointMeanCornerA 14 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 16, endpointJoint24Q (endpointMeanCornerK 14 16 h) (endpointMeanCornerA 14 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 14 16, endpointRunWeightQ (endpointMeanCutoff 14 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 14 16) = (43988853/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 14 16 h = (logRoundedQ ((endpointMeanCutoff 14 16:ℚ)/200)).2+(43988853/100000000000000:ℚ)+((endpointMeanRuns 14 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 14 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 14 16) r*endpointJoint24Q (endpointMeanCornerK 14 16 h) (endpointMeanCornerA 14 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 14 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 14 16 h≤endpointMeanCorner 14 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 14 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint14_16

namespace EndpointAnalyticJoint14_17
private noncomputable def weights : IntegerLookupTree := (.branch 1583 (.branch 1234 (.branch 1061 (.leaf (93047090900000:ℤ)) (.branch 1141 (.leaf (3529604100000:ℤ)) (.leaf (3473635400000:ℤ)))) (.branch 1343 (.leaf (3335765800000:ℤ)) (.branch 1474 (.leaf (3145235300000:ℤ)) (.leaf (1960258700000:ℤ))))) (.branch 2257 (.branch 1684 (.leaf (1421405500000:ℤ)) (.branch 1929 (.leaf (2626311500000:ℤ)) (.leaf (1914001500000:ℤ)))) (.branch 2720 (.leaf (1161727500000:ℤ)) (.branch 3422 (.leaf (513842400000:ℤ)) (.leaf (337416000000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 167 (.branch 147 (.branch 131 (.leaf (1881263225086586:ℤ)) (.branch 139 (.leaf (2111499751945053:ℤ)) (.leaf (2226206926787042:ℤ)))) (.branch 155 (.leaf (2349565974544940:ℤ)) (.branch 163 (.leaf (2482419464488660:ℤ)) (.leaf (2625711292060494:ℤ))))) (.branch 186 (.branch 172 (.leaf (2701597800832074:ℤ)) (.branch 179 (.leaf (2800716322801313:ℤ)) (.leaf (2947982247967528:ℤ)))) (.branch 193 (.leaf (3105992473725004:ℤ)) (.branch 200 (.leaf (3275758443611922:ℤ)) (.leaf (3458409097854814:ℤ)))))), (.branch 167 (.branch 147 (.branch 131 (.leaf (1888685965969717:ℤ)) (.branch 139 (.leaf (2123007430037084:ℤ)) (.leaf (2240039004838125:ℤ)))) (.branch 155 (.leaf (2366102733257606:ℤ)) (.branch 163 (.leaf (2502098484683876:ℤ)) (.leaf (2649036669337369:ℤ))))) (.branch 186 (.branch 172 (.leaf (2726959095865775:ℤ)) (.branch 179 (.leaf (2828843225022626:ℤ)) (.leaf (2980434943068935:ℤ)))) (.branch 193 (.leaf (3143365634555016:ℤ)) (.branch 200 (.leaf (3318728565602401:ℤ)) (.leaf (3507746827228085:ℤ)))))), (.branch 167 (.branch 147 (.branch 131 (.leaf (1886260670207368:ℤ)) (.branch 139 (.leaf (2119650922462936:ℤ)) (.leaf (2236232180606297:ℤ)))) (.branch 155 (.leaf (2361833348317312:ℤ)) (.branch 163 (.leaf (2497365379189422:ℤ)) (.leaf (2643853808430085:ℤ))))) (.branch 186 (.branch 172 (.leaf (2721562701261771:ℤ)) (.branch 179 (.leaf (2823196618159710:ℤ)) (.leaf (2974482357964006:ℤ)))) (.branch 193 (.leaf (3137180955929555:ℤ)) (.branch 200 (.leaf (3312416192131368:ℤ)) (.leaf (3501449613731027:ℤ)))))), (.branch 167 (.branch 147 (.branch 131 (.leaf (1893998671033803:ℤ)) (.branch 139 (.leaf (2131686102316796:ℤ)) (.leaf (2250721346119361:ℤ)))) (.branch 155 (.leaf (2379185141936273:ℤ)) (.branch 163 (.leaf (2518051841106897:ℤ)) (.leaf (2668420971201904:ℤ))))) (.branch 186 (.branch 172 (.leaf (2748301474929254:ℤ)) (.branch 179 (.leaf (2852890596449799:ℤ)) (.leaf (3008810247402153:ℤ)))) (.branch 193 (.leaf (3176795926340275:ℤ)) (.branch 200 (.leaf (3358064697811622:ℤ)) (.leaf (3553986126956918:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 14 17) 8000 (endpointMeanRuns 14 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 14 17, EndpointRunConditions (endpointMeanCutoff 14 17) (endpointMeanBox 14 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 14 17 h) (endpointMeanCornerA 14 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 14 17, endpointJoint24Q (endpointMeanCornerK 14 17 h) (endpointMeanCornerA 14 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 14 17, endpointRunWeightQ (endpointMeanCutoff 14 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 14 17) = (54815099/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 14 17 h = (logRoundedQ ((endpointMeanCutoff 14 17:ℚ)/200)).2+(54815099/125000000000000:ℚ)+((endpointMeanRuns 14 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 14 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 14 17) r*endpointJoint24Q (endpointMeanCornerK 14 17 h) (endpointMeanCornerA 14 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 14 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 14 17 h≤endpointMeanCorner 14 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 14 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint14_17

namespace EndpointAnalyticJoint15_03
private noncomputable def weights : IntegerLookupTree := (.branch 1664 (.branch 1032 (.leaf (142057858500000:ℤ)) (.leaf (35570911200000:ℤ))) (.branch 2242 (.leaf (6824452200000:ℤ)) (.leaf (9360553800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 146 (.leaf (1774378728983811:ℤ)) (.leaf (2125794980394069:ℤ))) (.branch 200 (.leaf (2317639923892677:ℤ)) (.leaf (2857322380575878:ℤ)))), (.branch 162 (.branch 146 (.leaf (1779018827973857:ℤ)) (.leaf (2135784906724351:ℤ))) (.branch 200 (.leaf (2331428434823393:ℤ)) (.leaf (2885133210836184:ℤ)))), (.branch 162 (.branch 146 (.leaf (1775312117247107:ℤ)) (.leaf (2128022698310336:ℤ))) (.branch 200 (.leaf (2320873607425439:ℤ)) (.leaf (2864717678306655:ℤ)))), (.branch 162 (.branch 146 (.leaf (1780136423259488:ℤ)) (.leaf (2138457952103168:ℤ))) (.branch 200 (.leaf (2335313499657399:ℤ)) (.leaf (2894052641941947:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 15 3) 8000 (endpointMeanRuns 15 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 15 3, EndpointRunConditions (endpointMeanCutoff 15 3) (endpointMeanBox 15 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 15 3 h) (endpointMeanCornerA 15 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 3, endpointJoint24Q (endpointMeanCornerK 15 3 h) (endpointMeanCornerA 15 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 15 3, endpointRunWeightQ (endpointMeanCutoff 15 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 15 3) = (456909947/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 15 3 h = (logRoundedQ ((endpointMeanCutoff 15 3:ℚ)/200)).2+(456909947/1000000000000000:ℚ)+((endpointMeanRuns 15 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 15 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 15 3) r*endpointJoint24Q (endpointMeanCornerK 15 3 h) (endpointMeanCornerA 15 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 15 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 15 3 h≤endpointMeanCorner 15 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 15 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint15_03

namespace EndpointAnalyticJoint15_04
private noncomputable def weights : IntegerLookupTree := (.branch 1664 (.branch 1032 (.leaf (138791594400000:ℤ)) (.leaf (35409952600000:ℤ))) (.branch 2242 (.leaf (6798868800000:ℤ)) (.leaf (9329631200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 146 (.leaf (1779018827973857:ℤ)) (.leaf (2135784906724351:ℤ))) (.branch 200 (.leaf (2331428434823393:ℤ)) (.leaf (2885133210836184:ℤ)))), (.branch 162 (.branch 146 (.leaf (1786176836424449:ℤ)) (.leaf (2151236452797139:ℤ))) (.branch 200 (.leaf (2352788986809016:ℤ)) (.leaf (2928422378412706:ℤ)))), (.branch 162 (.branch 146 (.leaf (1780136423259488:ℤ)) (.leaf (2138457952103168:ℤ))) (.branch 200 (.leaf (2335313499657399:ℤ)) (.leaf (2894052641941947:ℤ)))), (.branch 162 (.branch 146 (.leaf (1787579561560971:ℤ)) (.leaf (2154602458877311:ℤ))) (.branch 200 (.leaf (2357690831975856:ℤ)) (.leaf (2939743323449710:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 15 4) 8000 (endpointMeanRuns 15 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 15 4, EndpointRunConditions (endpointMeanCutoff 15 4) (endpointMeanBox 15 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 15 4 h) (endpointMeanCornerA 15 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 4, endpointJoint24Q (endpointMeanCornerK 15 4 h) (endpointMeanCornerA 15 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 15 4, endpointRunWeightQ (endpointMeanCutoff 15 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 15 4) = (113962849/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 15 4 h = (logRoundedQ ((endpointMeanCutoff 15 4:ℚ)/200)).2+(113962849/250000000000000:ℚ)+((endpointMeanRuns 15 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 15 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 15 4) r*endpointJoint24Q (endpointMeanCornerK 15 4 h) (endpointMeanCornerA 15 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 15 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 15 4 h≤endpointMeanCorner 15 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 15 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint15_04

namespace EndpointAnalyticJoint15_05
private noncomputable def weights : IntegerLookupTree := (.branch 1664 (.branch 1032 (.leaf (134031633800000:ℤ)) (.leaf (35171256300000:ℤ))) (.branch 2242 (.leaf (6760929500000:ℤ)) (.leaf (9283774200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 146 (.leaf (1786176836424449:ℤ)) (.leaf (2151236452797139:ℤ))) (.branch 200 (.leaf (2352788986809016:ℤ)) (.leaf (2928422378412706:ℤ)))), (.branch 162 (.branch 146 (.leaf (1793363645629806:ℤ)) (.leaf (2166799784600454:ℤ))) (.branch 200 (.leaf (2374345244214678:ℤ)) (.leaf (2972361066095418:ℤ)))), (.branch 162 (.branch 146 (.leaf (1787579561560971:ℤ)) (.leaf (2154602458877311:ℤ))) (.branch 200 (.leaf (2357690831975856:ℤ)) (.leaf (2939743323449710:ℤ)))), (.branch 162 (.branch 146 (.leaf (1795053821245655:ℤ)) (.leaf (2170868850254669:ℤ))) (.branch 200 (.leaf (2380282587326491:ℤ)) (.leaf (2986155359623377:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 15 5) 8000 (endpointMeanRuns 15 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 15 5, EndpointRunConditions (endpointMeanCutoff 15 5) (endpointMeanBox 15 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 15 5 h) (endpointMeanCornerA 15 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 5, endpointJoint24Q (endpointMeanCornerK 15 5 h) (endpointMeanCornerA 15 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 15 5, endpointRunWeightQ (endpointMeanCutoff 15 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 15 5) = (141963/312500000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 15 5 h = (logRoundedQ ((endpointMeanCutoff 15 5:ℚ)/200)).2+(141963/312500000000:ℚ)+((endpointMeanRuns 15 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 15 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 15 5) r*endpointJoint24Q (endpointMeanCornerK 15 5 h) (endpointMeanCornerA 15 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 15 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 15 5 h≤endpointMeanCorner 15 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 15 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint15_05

namespace EndpointAnalyticJoint15_06
private noncomputable def weights : IntegerLookupTree := (.branch 1258 (.branch 1032 (.leaf (129433545600000:ℤ)) (.leaf (12418318400000:ℤ))) (.branch 1664 (.leaf (13109834600000:ℤ)) (.branch 2242 (.leaf (6723500500000:ℤ)) (.leaf (9238534100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 146 (.leaf (1793363645629806:ℤ)) (.leaf (2166799784600454:ℤ))) (.branch 182 (.leaf (2374345244214678:ℤ)) (.branch 200 (.leaf (2668624005317612:ℤ)) (.leaf (2972361066095418:ℤ))))), (.branch 162 (.branch 146 (.leaf (1800579371471804:ℤ)) (.leaf (2182475710859160:ℤ))) (.branch 182 (.leaf (2396099000093829:ℤ)) (.branch 200 (.leaf (2700643694728259:ℤ)) (.leaf (3016959019425568:ℤ))))), (.branch 162 (.branch 146 (.leaf (1795053821245655:ℤ)) (.leaf (2170868850254669:ℤ))) (.branch 182 (.leaf (2380282587326491:ℤ)) (.branch 200 (.leaf (2677947468642786:ℤ)) (.leaf (2986155359623377:ℤ))))), (.branch 162 (.branch 146 (.leaf (1802559332438821:ℤ)) (.leaf (2187258046415505:ℤ))) (.branch 182 (.leaf (2403090820343708:ℤ)) (.branch 200 (.leaf (2711654783391501:ℤ)) (.leaf (3033300139055482:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 15 6) 8000 (endpointMeanRuns 15 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 15 6, EndpointRunConditions (endpointMeanCutoff 15 6) (endpointMeanBox 15 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 15 6 h) (endpointMeanCornerA 15 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 6, endpointJoint24Q (endpointMeanCornerK 15 6 h) (endpointMeanCornerA 15 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 15 6, endpointRunWeightQ (endpointMeanCutoff 15 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 15 6) = (226366461/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 15 6 h = (logRoundedQ ((endpointMeanCutoff 15 6:ℚ)/200)).2+(226366461/500000000000000:ℚ)+((endpointMeanRuns 15 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 15 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 15 6) r*endpointJoint24Q (endpointMeanCornerK 15 6 h) (endpointMeanCornerA 15 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 15 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 15 6 h≤endpointMeanCorner 15 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 15 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint15_06

namespace EndpointAnalyticJoint15_07
private noncomputable def weights : IntegerLookupTree := (.branch 1258 (.branch 1032 (.leaf (125721195400000:ℤ)) (.leaf (12346576300000:ℤ))) (.branch 1664 (.leaf (13041961500000:ℤ)) (.branch 2242 (.leaf (6692689800000:ℤ)) (.leaf (9201293400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 146 (.leaf (1800579371471804:ℤ)) (.leaf (2182475710859160:ℤ))) (.branch 182 (.leaf (2396099000093829:ℤ)) (.branch 200 (.leaf (2700643694728259:ℤ)) (.leaf (3016959019425568:ℤ))))), (.branch 162 (.branch 146 (.leaf (1807824130298579:ℤ)) (.leaf (2198265046148928:ℤ))) (.branch 182 (.leaf (2418052063927883:ℤ)) (.branch 200 (.leaf (2733047574833400:ℤ)) (.leaf (3062226130168636:ℤ))))), (.branch 162 (.branch 146 (.leaf (1802559332438821:ℤ)) (.leaf (2187258046415505:ℤ))) (.branch 182 (.leaf (2403090820343708:ℤ)) (.branch 200 (.leaf (2711654783391501:ℤ)) (.leaf (3033300139055482:ℤ))))), (.branch 162 (.branch 146 (.leaf (1810096225809841:ℤ)) (.leaf (2203770974487071:ℤ))) (.branch 182 (.leaf (2426117605349723:ℤ)) (.branch 200 (.leaf (2745786371984592:ℤ)) (.leaf (3081189230139201:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 15 7) 8000 (endpointMeanRuns 15 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 15 7, EndpointRunConditions (endpointMeanCutoff 15 7) (endpointMeanBox 15 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 15 7 h) (endpointMeanCornerA 15 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 7, endpointJoint24Q (endpointMeanCornerK 15 7 h) (endpointMeanCornerA 15 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 15 7, endpointRunWeightQ (endpointMeanCutoff 15 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 15 7) = (90291617/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 15 7 h = (logRoundedQ ((endpointMeanCutoff 15 7:ℚ)/200)).2+(90291617/200000000000000:ℚ)+((endpointMeanRuns 15 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 15 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 15 7) r*endpointJoint24Q (endpointMeanCornerK 15 7 h) (endpointMeanCornerA 15 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 15 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 15 7 h≤endpointMeanCorner 15 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 15 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint15_07

namespace EndpointAnalyticJoint15_08
private noncomputable def weights : IntegerLookupTree := (.branch 1664 (.branch 1032 (.leaf (121404730400000:ℤ)) (.branch 1258 (.leaf (12261521600000:ℤ)) (.leaf (12961493700000:ℤ)))) (.branch 2242 (.leaf (6656161800000:ℤ)) (.branch 3438 (.leaf (2792416700000:ℤ)) (.leaf (366897200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 130 (.leaf (1807824130298579:ℤ)) (.branch 146 (.leaf (2002775062962968:ℤ)) (.leaf (2198265046148928:ℤ)))) (.branch 182 (.leaf (2418052063927883:ℤ)) (.branch 200 (.leaf (2733047574833400:ℤ)) (.leaf (3062226130168636:ℤ))))), (.branch 162 (.branch 130 (.leaf (1815098038926408:ℤ)) (.branch 146 (.leaf (2013955037551945:ℤ)) (.leaf (2214168610938545:ℤ)))) (.branch 182 (.leaf (2440206261776712:ℤ)) (.branch 200 (.leaf (2765840255374494:ℤ)) (.leaf (3108172438508295:ℤ))))), (.branch 162 (.branch 130 (.leaf (1810096225809841:ℤ)) (.branch 146 (.leaf (2006460429053424:ℤ)) (.leaf (2203770974487071:ℤ)))) (.branch 182 (.leaf (2426117605349723:ℤ)) (.branch 200 (.leaf (2745786371984592:ℤ)) (.leaf (3081189230139201:ℤ))))), (.branch 162 (.branch 130 (.leaf (1817664632574433:ℤ)) (.branch 146 (.leaf (2018124697816276:ℤ)) (.leaf (2220408568596081:ℤ)))) (.branch 182 (.leaf (2449365036543238:ℤ)) (.branch 200 (.leaf (2780347574755357:ℤ)) (.leaf (3129834383907024:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 15 8) 8000 (endpointMeanRuns 15 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 15 8, EndpointRunConditions (endpointMeanCutoff 15 8) (endpointMeanBox 15 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 15 8 h) (endpointMeanCornerA 15 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 8, endpointJoint24Q (endpointMeanCornerK 15 8 h) (endpointMeanCornerA 15 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 15 8, endpointRunWeightQ (endpointMeanCutoff 15 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 15 8) = (224973343/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 15 8 h = (logRoundedQ ((endpointMeanCutoff 15 8:ℚ)/200)).2+(224973343/500000000000000:ℚ)+((endpointMeanRuns 15 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 15 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 15 8) r*endpointJoint24Q (endpointMeanCornerK 15 8 h) (endpointMeanCornerA 15 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 15 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 15 8 h≤endpointMeanCorner 15 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 15 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint15_08

namespace EndpointAnalyticJoint15_09
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1032 (.leaf (117234048500000:ℤ)) (.branch 1258 (.leaf (12177569100000:ℤ)) (.leaf (6971786400000:ℤ)))) (.branch 2242 (.branch 1664 (.leaf (3748537600000:ℤ)) (.leaf (6620107200000:ℤ))) (.branch 3438 (.leaf (2779001800000:ℤ)) (.leaf (365366400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 130 (.leaf (1815098038926408:ℤ)) (.branch 146 (.leaf (2013955037551945:ℤ)) (.leaf (2214168610938545:ℤ)))) (.branch 182 (.branch 170 (.leaf (2440206261776712:ℤ)) (.leaf (2564244896575016:ℤ))) (.branch 200 (.leaf (2765840255374494:ℤ)) (.leaf (3108172438508295:ℤ))))), (.branch 162 (.branch 130 (.leaf (1822401214641579:ℤ)) (.branch 146 (.leaf (2025197421461932:ℤ)) (.leaf (2230187231632571:ℤ)))) (.branch 182 (.branch 170 (.leaf (2462563436430574:ℤ)) (.leaf (2590494909490192:ℤ))) (.branch 200 (.leaf (2799026401403338:ℤ)) (.leaf (3154808135273336:ℤ))))), (.branch 162 (.branch 130 (.leaf (1817664632574433:ℤ)) (.branch 146 (.leaf (2018124697816276:ℤ)) (.leaf (2220408568596081:ℤ)))) (.branch 182 (.branch 170 (.leaf (2449365036543238:ℤ)) (.leaf (2575278298153480:ℤ))) (.branch 200 (.leaf (2780347574755357:ℤ)) (.leaf (3129834383907024:ℤ))))), (.branch 162 (.branch 130 (.leaf (1825264684496968:ℤ)) (.branch 146 (.leaf (2029856775125863:ℤ)) (.leaf (2237171769921507:ℤ)))) (.branch 182 (.branch 170 (.leaf (2472835228189872:ℤ)) (.leaf (2602882699366147:ℤ))) (.branch 200 (.leaf (2815343799255831:ℤ)) (.leaf (3179247536914214:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 15 9) 8000 (endpointMeanRuns 15 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 15 9, EndpointRunConditions (endpointMeanCutoff 15 9) (endpointMeanBox 15 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 15 9 h) (endpointMeanCornerA 15 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 9, endpointJoint24Q (endpointMeanCornerK 15 9 h) (endpointMeanCornerA 15 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 15 9, endpointRunWeightQ (endpointMeanCutoff 15 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 15 9) = (448454873/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 15 9 h = (logRoundedQ ((endpointMeanCutoff 15 9:ℚ)/200)).2+(448454873/1000000000000000:ℚ)+((endpointMeanRuns 15 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 15 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 15 9) r*endpointJoint24Q (endpointMeanCornerK 15 9 h) (endpointMeanCornerA 15 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 15 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 15 9 h≤endpointMeanCorner 15 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 15 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint15_09

namespace EndpointAnalyticJoint15_10
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1032 (.leaf (113866055200000:ℤ)) (.branch 1258 (.leaf (12108430300000:ℤ)) (.leaf (6935696900000:ℤ)))) (.branch 2242 (.branch 1664 (.leaf (3730394700000:ℤ)) (.leaf (6590414600000:ℤ))) (.branch 3438 (.leaf (2767953900000:ℤ)) (.leaf (364105700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 130 (.leaf (1822401214641579:ℤ)) (.branch 146 (.leaf (2025197421461932:ℤ)) (.leaf (2230187231632571:ℤ)))) (.branch 182 (.branch 170 (.leaf (2462563436430574:ℤ)) (.leaf (2590494909490192:ℤ))) (.branch 200 (.leaf (2799026401403338:ℤ)) (.leaf (3154808135273336:ℤ))))), (.branch 162 (.branch 130 (.leaf (1829733775202299:ℤ)) (.branch 146 (.leaf (2036502563076846:ℤ)) (.leaf (2246321740614272:ℤ)))) (.branch 182 (.branch 170 (.leaf (2485125447563352:ℤ)) (.leaf (2617013642128260:ℤ))) (.branch 200 (.leaf (2832610733945703:ℤ)) (.leaf (3202143564197969:ℤ))))), (.branch 162 (.branch 130 (.leaf (1825264684496968:ℤ)) (.branch 146 (.leaf (2029856775125863:ℤ)) (.leaf (2237171769921507:ℤ)))) (.branch 182 (.branch 170 (.leaf (2472835228189872:ℤ)) (.leaf (2602882699366147:ℤ))) (.branch 200 (.leaf (2815343799255831:ℤ)) (.leaf (3179247536914214:ℤ))))), (.branch 162 (.branch 130 (.leaf (1832896513892746:ℤ)) (.branch 146 (.leaf (2041657055177402:ℤ)) (.leaf (2254061526747870:ℤ)))) (.branch 182 (.branch 170 (.leaf (2496530314814476:ℤ)) (.leaf (2630782992081825:ℤ))) (.branch 200 (.leaf (2850780521102901:ℤ)) (.leaf (3229440814167809:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 15 10) 8000 (endpointMeanRuns 15 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 15 10, EndpointRunConditions (endpointMeanCutoff 15 10) (endpointMeanBox 15 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 15 10 h) (endpointMeanCornerA 15 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 10, endpointJoint24Q (endpointMeanCornerK 15 10 h) (endpointMeanCornerA 15 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 15 10, endpointRunWeightQ (endpointMeanCutoff 15 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 15 10) = (55903287/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 15 10 h = (logRoundedQ ((endpointMeanCutoff 15 10:ℚ)/200)).2+(55903287/125000000000000:ℚ)+((endpointMeanRuns 15 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 15 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 15 10) r*endpointJoint24Q (endpointMeanCornerK 15 10 h) (endpointMeanCornerA 15 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 15 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 15 10 h≤endpointMeanCorner 15 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 15 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint15_10

namespace EndpointAnalyticJoint15_11
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1134 (.branch 1032 (.leaf (109949183700000:ℤ)) (.leaf (5332167800000:ℤ))) (.branch 1258 (.leaf (5230067000000:ℤ)) (.leaf (6892891800000:ℤ)))) (.branch 1910 (.branch 1664 (.leaf (3708875700000:ℤ)) (.leaf (3041793000000:ℤ))) (.branch 2242 (.leaf (2222662900000:ℤ)) (.branch 3438 (.leaf (2754850300000:ℤ)) (.leaf (362610400000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 146 (.branch 130 (.leaf (1829733775202299:ℤ)) (.leaf (2036502563076846:ℤ))) (.branch 154 (.leaf (2246321740614272:ℤ)) (.leaf (2361793953446099:ℤ)))) (.branch 182 (.branch 170 (.leaf (2485125447563352:ℤ)) (.leaf (2617013642128260:ℤ))) (.branch 191 (.leaf (2832610733945703:ℤ)) (.branch 200 (.leaf (3009891639181956:ℤ)) (.leaf (3202143564197969:ℤ)))))), (.branch 162 (.branch 146 (.branch 130 (.leaf (1837095838840577:ℤ)) (.leaf (2047870812725362:ℤ))) (.branch 154 (.leaf (2262572976288860:ℤ)) (.leaf (2381071759631575:ℤ)))) (.branch 182 (.branch 170 (.leaf (2507894171887284:ℤ)) (.leaf (2643803845356047:ℤ))) (.branch 191 (.leaf (2866598030672958:ℤ)) (.branch 200 (.leaf (3050358101357273:ℤ)) (.leaf (3250189224216029:ℤ)))))), (.branch 162 (.branch 146 (.branch 130 (.leaf (1832896513892746:ℤ)) (.leaf (2041657055177402:ℤ))) (.branch 154 (.leaf (2254061526747870:ℤ)) (.leaf (2371208092347161:ℤ)))) (.branch 182 (.branch 170 (.leaf (2496530314814476:ℤ)) (.leaf (2630782992081825:ℤ))) (.branch 191 (.leaf (2850780521102901:ℤ)) (.branch 200 (.leaf (3032187251036977:ℤ)) (.leaf (3229440814167809:ℤ)))))), (.branch 162 (.branch 146 (.branch 130 (.leaf (1840560253630305:ℤ)) (.leaf (2053525934457720:ℤ))) (.branch 154 (.leaf (2271078794518850:ℤ)) (.leaf (2391427430168125:ℤ)))) (.branch 182 (.branch 170 (.leaf (2520452451395238:ℤ)) (.leaf (2658982347960741:ℤ))) (.branch 191 (.leaf (2886663284835010:ℤ)) (.branch 200 (.leaf (3075015871436980:ℤ)) (.leaf (3280426532101846:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 15 11) 8000 (endpointMeanRuns 15 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 15 11, EndpointRunConditions (endpointMeanCutoff 15 11) (endpointMeanBox 15 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 15 11 h) (endpointMeanCornerA 15 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 11, endpointJoint24Q (endpointMeanCornerK 15 11 h) (endpointMeanCornerA 15 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 15 11, endpointRunWeightQ (endpointMeanCutoff 15 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 15 11) = (27860569/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 15 11 h = (logRoundedQ ((endpointMeanCutoff 15 11:ℚ)/200)).2+(27860569/62500000000000:ℚ)+((endpointMeanRuns 15 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 15 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 15 11) r*endpointJoint24Q (endpointMeanCornerK 15 11 h) (endpointMeanCornerA 15 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 15 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 15 11 h≤endpointMeanCorner 15 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 15 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint15_11

namespace EndpointAnalyticJoint15_12
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1134 (.branch 1032 (.leaf (106163787100000:ℤ)) (.branch 1064 (.leaf (1636581100000:ℤ)) (.leaf (3380786800000:ℤ)))) (.branch 1258 (.branch 1186 (.leaf (2166450600000:ℤ)) (.leaf (2692070000000:ℤ))) (.branch 1340 (.leaf (2623140300000:ℤ)) (.leaf (3559844600000:ℤ))))) (.branch 1910 (.branch 1563 (.leaf (1765221700000:ℤ)) (.branch 1664 (.leaf (1633666300000:ℤ)) (.leaf (3025323500000:ℤ)))) (.branch 2714 (.branch 2242 (.leaf (2211337800000:ℤ)) (.leaf (1333245100000:ℤ))) (.branch 3438 (.leaf (578729700000:ℤ)) (.leaf (361133800000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 170 (.branch 146 (.branch 130 (.leaf (1837095838840577:ℤ)) (.branch 138 (.leaf (2047870812725362:ℤ)) (.leaf (2151711850001382:ℤ)))) (.branch 162 (.branch 154 (.leaf (2262572976288860:ℤ)) (.leaf (2381071759631575:ℤ))) (.branch 166 (.leaf (2507894171887284:ℤ)) (.leaf (2574662057756553:ℤ))))) (.branch 187 (.branch 177 (.leaf (2643803845356047:ℤ)) (.branch 182 (.leaf (2770846619429438:ℤ)) (.leaf (2866598030672958:ℤ)))) (.branch 197 (.branch 191 (.leaf (2966804457058282:ℤ)) (.leaf (3050358101357273:ℤ))) (.branch 200 (.leaf (3181683690689912:ℤ)) (.leaf (3250189224216029:ℤ)))))), (.branch 170 (.branch 146 (.branch 130 (.leaf (1844487524264139:ℤ)) (.branch 138 (.leaf (2059302522691787:ℤ)) (.leaf (2165430194463825:ℤ)))) (.branch 162 (.branch 154 (.leaf (2278941783127091:ℤ)) (.leaf (2400506918159658:ℤ))) (.branch 166 (.leaf (2530871503309038:ℤ)) (.leaf (2599610110492731:ℤ))))) (.branch 187 (.branch 177 (.leaf (2670868298200807:ℤ)) (.branch 182 (.leaf (2801996844183820:ℤ)) (.leaf (2900993126581715:ℤ)))) (.branch 197 (.branch 191 (.leaf (3004744539690990:ℤ)) (.leaf (3091368614534179:ℤ))) (.branch 200 (.leaf (3227726638752682:ℤ)) (.leaf (3298955771789655:ℤ)))))), (.branch 170 (.branch 146 (.branch 130 (.leaf (1840560253630305:ℤ)) (.branch 138 (.leaf (2053525934457720:ℤ)) (.leaf (2158666100992367:ℤ)))) (.branch 162 (.branch 154 (.leaf (2271078794518850:ℤ)) (.leaf (2391427430168125:ℤ))) (.branch 166 (.leaf (2520452451395238:ℤ)) (.leaf (2588473731839948:ℤ))))) (.branch 187 (.branch 177 (.leaf (2658982347960741:ℤ)) (.branch 182 (.leaf (2788720883383833:ℤ)) (.leaf (2886663284835010:ℤ)))) (.branch 197 (.branch 191 (.leaf (2989310542017197:ℤ)) (.leaf (3075015871436980:ℤ))) (.branch 200 (.leaf (3209939054994366:ℤ)) (.leaf (3280426532101846:ℤ)))))), (.branch 170 (.branch 146 (.branch 130 (.leaf (1848256037133740:ℤ)) (.branch 138 (.leaf (2065463811758547:ℤ)) (.leaf (2173013018300653:ℤ)))) (.branch 162 (.branch 154 (.leaf (2288224535891346:ℤ)) (.leaf (2411819178678490:ℤ))) (.branch 166 (.leaf (2544603813559683:ℤ)) (.leaf (2614721114334233:ℤ))))) (.branch 187 (.branch 177 (.leaf (2687483972660154:ℤ)) (.branch 182 (.leaf (2821583573238881:ℤ)) (.leaf (2922997704779701:ℤ)))) (.branch 197 (.branch 191 (.leaf (3029445715464594:ℤ)) (.leaf (3118449431629115:ℤ))) (.branch 200 (.leaf (3258791040829719:ℤ)) (.leaf (3332217201599585:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 15 12) 8000 (endpointMeanRuns 15 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 15 12, EndpointRunConditions (endpointMeanCutoff 15 12) (endpointMeanBox 15 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 15 12 h) (endpointMeanCornerA 15 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 12, endpointJoint24Q (endpointMeanCornerK 15 12 h) (endpointMeanCornerA 15 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 15 12, endpointRunWeightQ (endpointMeanCutoff 15 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 15 12) = (27770633/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 15 12 h = (logRoundedQ ((endpointMeanCutoff 15 12:ℚ)/200)).2+(27770633/62500000000000:ℚ)+((endpointMeanRuns 15 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 15 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 15 12) r*endpointJoint24Q (endpointMeanCornerK 15 12 h) (endpointMeanCornerA 15 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 15 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 15 12 h≤endpointMeanCorner 15 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 15 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint15_12

namespace EndpointAnalyticJoint15_13
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1214 (.branch 1109 (.branch 1032 (.leaf (103106348200000:ℤ)) (.branch 1064 (.leaf (1627076600000:ℤ)) (.leaf (2154624800000:ℤ)))) (.branch 1134 (.leaf (1087028100000:ℤ)) (.branch 1186 (.leaf (2154547000000:ℤ)) (.leaf (1038908200000:ℤ))))) (.branch 1340 (.branch 1258 (.leaf (1541096700000:ℤ)) (.branch 1306 (.leaf (1530013700000:ℤ)) (.leaf (978427700000:ℤ)))) (.branch 1394 (.leaf (1441856900000:ℤ)) (.branch 1433 (.leaf (927103500000:ℤ)) (.leaf (894466700000:ℤ)))))) (.branch 2242 (.branch 1778 (.branch 1563 (.leaf (1756738000000:ℤ)) (.branch 1664 (.leaf (1626029900000:ℤ)) (.leaf (1453765000000:ℤ)))) (.branch 1910 (.leaf (1285835200000:ℤ)) (.branch 2063 (.leaf (1086703400000:ℤ)) (.leaf (877528400000:ℤ))))) (.branch 3033 (.branch 2456 (.leaf (674274700000:ℤ)) (.branch 2714 (.leaf (476334200000:ℤ)) (.leaf (305746500000:ℤ)))) (.branch 3438 (.leaf (170208000000:ℤ)) (.branch 4687 (.leaf (136219100000:ℤ)) (.leaf (11948500000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 170 (.branch 146 (.branch 134 (.branch 122 (.leaf (1844487524264139:ℤ)) (.branch 130 (.leaf (1959956300357340:ℤ)) (.leaf (2059302522691787:ℤ)))) (.branch 138 (.leaf (2111482499491593:ℤ)) (.branch 142 (.leaf (2165430194463825:ℤ)) (.leaf (2221222821664483:ℤ))))) (.branch 158 (.branch 150 (.leaf (2278941783127091:ℤ)) (.branch 154 (.leaf (2338672942251813:ℤ)) (.leaf (2400506918159658:ℤ)))) (.branch 162 (.leaf (2464539402865399:ℤ)) (.branch 166 (.leaf (2530871503309038:ℤ)) (.leaf (2599610110492731:ℤ)))))) (.branch 185 (.branch 177 (.branch 172 (.leaf (2670868298200807:ℤ)) (.branch 174 (.leaf (2707479366278851:ℤ)) (.leaf (2744765754038005:ℤ)))) (.branch 179 (.leaf (2801996844183820:ℤ)) (.branch 182 (.leaf (2841042882065753:ℤ)) (.leaf (2900993126581715:ℤ))))) (.branch 193 (.branch 187 (.leaf (2962654809320353:ℤ)) (.branch 191 (.leaf (3004744539690990:ℤ)) (.leaf (3091368614534179:ℤ)))) (.branch 197 (.leaf (3135943706399580:ℤ)) (.branch 200 (.leaf (3227726638752682:ℤ)) (.leaf (3298955771789655:ℤ))))))), (.branch 170 (.branch 146 (.branch 134 (.branch 122 (.leaf (1851908950658341:ℤ)) (.branch 130 (.leaf (1969465812357496:ℤ)) (.leaf (2070798047226959:ℤ)))) (.branch 138 (.leaf (2124089856322212:ℤ)) (.branch 142 (.leaf (2179236000904408:ℤ)) (.leaf (2236319751682715:ℤ))))) (.branch 158 (.branch 150 (.leaf (2295429011709116:ℤ)) (.branch 154 (.leaf (2356656625673118:ℤ)) (.leaf (2420100713396393:ℤ)))) (.branch 162 (.leaf (2485865029706007:ℤ)) (.branch 166 (.leaf (2554059353087262:ℤ)) (.leaf (2624799905764966:ℤ)))))) (.branch 185 (.branch 177 (.branch 172 (.leaf (2698209808138551:ℤ)) (.branch 174 (.leaf (2735956247062147:ℤ)) (.leaf (2774419570805270:ℤ)))) (.branch 179 (.leaf (2833497263891411:ℤ)) (.branch 182 (.leaf (2873830773943298:ℤ)) (.leaf (2935800914681675:ℤ))))) (.branch 193 (.branch 187 (.leaf (2999594082927079:ℤ)) (.branch 191 (.leaf (3043169807610092:ℤ)) (.leaf (3132930493201680:ℤ)))) (.branch 197 (.leaf (3179160239525638:ℤ)) (.branch 200 (.leaf (3274435885942711:ℤ)) (.leaf (3348454023272868:ℤ))))))), (.branch 170 (.branch 146 (.branch 134 (.branch 122 (.leaf (1848256037133740:ℤ)) (.branch 130 (.leaf (1964931385082545:ℤ)) (.leaf (2065463811758547:ℤ)))) (.branch 138 (.leaf (2118322621273172:ℤ)) (.branch 142 (.leaf (2173013018300653:ℤ)) (.leaf (2229617819787291:ℤ))))) (.branch 158 (.branch 150 (.leaf (2288224535891346:ℤ)) (.branch 154 (.leaf (2348925692298710:ℤ)) (.leaf (2411819178678490:ℤ)))) (.branch 162 (.leaf (2477008625733106:ℤ)) (.branch 166 (.leaf (2544603813559683:ℤ)) (.leaf (2614721114334233:ℤ)))))) (.branch 185 (.branch 177 (.branch 172 (.leaf (2687483972660154:ℤ)) (.branch 174 (.leaf (2724898123689979:ℤ)) (.leaf (2763023427293827:ℤ)))) (.branch 179 (.leaf (2821583573238881:ℤ)) (.branch 182 (.leaf (2861565223363527:ℤ)) (.leaf (2922997704779701:ℤ))))) (.branch 193 (.branch 187 (.leaf (2986241905574818:ℤ)) (.branch 191 (.leaf (3029445715464594:ℤ)) (.leaf (3118449431629115:ℤ)))) (.branch 197 (.leaf (3164294694174195:ℤ)) (.branch 200 (.leaf (3258791040829719:ℤ)) (.leaf (3332217201599585:ℤ))))))), (.branch 170 (.branch 146 (.branch 134 (.branch 122 (.leaf (1855983998385017:ℤ)) (.branch 130 (.leaf (1974850116543036:ℤ)) (.leaf (2077471088189938:ℤ)))) (.branch 138 (.leaf (2131501046709361:ℤ)) (.branch 142 (.leaf (2187455288028724:ℤ)) (.leaf (2245423287643090:ℤ))))) (.branch 158 (.branch 150 (.leaf (2305499720789942:ℤ)) (.branch 154 (.leaf (2367784827531418:ℤ)) (.leaf (2432384808027581:ℤ)))) (.branch 162 (.leaf (2499412250885592:ℤ)) (.branch 166 (.leaf (2568986597782521:ℤ)) (.leaf (2641234647911807:ℤ)))))) (.branch 185 (.branch 177 (.branch 172 (.leaf (2716291106198739:ℤ)) (.branch 174 (.leaf (2754916891113382:ℤ)) (.leaf (2794299179675553:ℤ)))) (.branch 179 (.leaf (2854833521779783:ℤ)) (.branch 182 (.leaf (2896193017154955:ℤ)) (.leaf (2959789465932028:ℤ))))) (.branch 193 (.branch 187 (.leaf (3025320140582396:ℤ)) (.branch 191 (.leaf (3070119753016268:ℤ)) (.leaf (3162496476183559:ℤ)))) (.branch 197 (.leaf (3210123565558185:ℤ)) (.branch 200 (.leaf (3308386503871072:ℤ)) (.leaf (3384825531063426:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 15 13) 8000 (endpointMeanRuns 15 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 15 13, EndpointRunConditions (endpointMeanCutoff 15 13) (endpointMeanBox 15 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 15 13 h) (endpointMeanCornerA 15 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 13, endpointJoint24Q (endpointMeanCornerK 15 13 h) (endpointMeanCornerA 15 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 15 13, endpointRunWeightQ (endpointMeanCutoff 15 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 15 13) = (44314457/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 15 13 h = (logRoundedQ ((endpointMeanCutoff 15 13:ℚ)/200)).2+(44314457/100000000000000:ℚ)+((endpointMeanRuns 15 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 15 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 15 13) r*endpointJoint24Q (endpointMeanCornerK 15 13 h) (endpointMeanCornerA 15 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 15 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 15 13 h≤endpointMeanCorner 15 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 15 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint15_13

namespace EndpointAnalyticJoint15_14
private noncomputable def weights : IntegerLookupTree := (.branch 1517 (.branch 1214 (.branch 1109 (.branch 1064 (.branch 1032 (.leaf (99549995500000:ℤ)) (.leaf (1615799100000:ℤ))) (.branch 1086 (.leaf (1040713700000:ℤ)) (.leaf (1041974600000:ℤ)))) (.branch 1159 (.branch 1134 (.leaf (1079773700000:ℤ)) (.leaf (1027058100000:ℤ))) (.branch 1186 (.leaf (1052911800000:ℤ)) (.leaf (1032222000000:ℤ))))) (.branch 1306 (.branch 1258 (.branch 1243 (.leaf (1008806000000:ℤ)) (.leaf (491144600000:ℤ))) (.branch 1289 (.leaf (983885100000:ℤ)) (.leaf (504859000000:ℤ)))) (.branch 1394 (.branch 1340 (.leaf (972438400000:ℤ)) (.leaf (1433171000000:ℤ))) (.branch 1433 (.leaf (921610300000:ℤ)) (.branch 1474 (.leaf (889237600000:ℤ)) (.leaf (852285000000:ℤ))))))) (.branch 2063 (.branch 1719 (.branch 1612 (.branch 1563 (.leaf (828303700000:ℤ)) (.leaf (795547700000:ℤ))) (.branch 1664 (.leaf (755787900000:ℤ)) (.leaf (710789900000:ℤ)))) (.branch 1842 (.branch 1778 (.leaf (672456200000:ℤ)) (.leaf (636046800000:ℤ))) (.branch 1910 (.leaf (582867200000:ℤ)) (.branch 1983 (.leaf (534201900000:ℤ)) (.leaf (492440700000:ℤ)))))) (.branch 2456 (.branch 2242 (.branch 2149 (.leaf (438205900000:ℤ)) (.leaf (386415500000:ℤ))) (.branch 2344 (.leaf (339023300000:ℤ)) (.leaf (290932200000:ℤ)))) (.branch 3033 (.branch 2714 (.leaf (474145100000:ℤ)) (.leaf (304394000000:ℤ))) (.branch 3438 (.leaf (169485100000:ℤ)) (.branch 4687 (.leaf (135670300000:ℤ)) (.leaf (11904700000:ℤ))))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 148 (.branch 138 (.branch 130 (.branch 122 (.leaf (1851908950658341:ℤ)) (.leaf (1969465812357496:ℤ))) (.branch 134 (.leaf (2070798047226959:ℤ)) (.leaf (2124089856322212:ℤ)))) (.branch 144 (.branch 142 (.leaf (2179236000904408:ℤ)) (.leaf (2236319751682715:ℤ))) (.branch 146 (.leaf (2265615509851319:ℤ)) (.leaf (2295429011709116:ℤ))))) (.branch 156 (.branch 152 (.branch 150 (.leaf (2325772019678817:ℤ)) (.leaf (2356656625673118:ℤ))) (.branch 154 (.leaf (2388095262116406:ℤ)) (.leaf (2420100713396393:ℤ)))) (.branch 160 (.branch 158 (.leaf (2452686127764595:ℤ)) (.leaf (2485865029706007:ℤ))) (.branch 162 (.leaf (2519651332798883:ℤ)) (.branch 164 (.leaf (2554059353087262:ℤ)) (.leaf (2589103822989064:ℤ))))))) (.branch 183 (.branch 174 (.branch 170 (.branch 168 (.leaf (2624799905764966:ℤ)) (.leaf (2661163210573274:ℤ))) (.branch 172 (.leaf (2698209808138551:ℤ)) (.leaf (2735956247062147:ℤ)))) (.branch 179 (.branch 177 (.leaf (2774419570805270:ℤ)) (.leaf (2833497263891411:ℤ))) (.branch 180 (.leaf (2873830773943298:ℤ)) (.branch 182 (.leaf (2894289085080511:ℤ)) (.leaf (2935800914681675:ℤ)))))) (.branch 191 (.branch 187 (.branch 185 (.leaf (2956859382393420:ℤ)) (.leaf (2999594082927079:ℤ))) (.branch 189 (.leaf (3043169807610092:ℤ)) (.leaf (3087607929556071:ℤ)))) (.branch 195 (.branch 193 (.leaf (3132930493201680:ℤ)) (.leaf (3179160239525638:ℤ))) (.branch 197 (.leaf (3226320632373399:ℤ)) (.branch 200 (.leaf (3274435885942711:ℤ)) (.leaf (3348454023272868:ℤ)))))))), (.branch 166 (.branch 148 (.branch 138 (.branch 130 (.branch 122 (.leaf (1859360237688077:ℤ)) (.leaf (1979021463559056:ℤ))) (.branch 134 (.leaf (2082357742559222:ℤ)) (.leaf (2136772489858315:ℤ)))) (.branch 144 (.branch 142 (.leaf (2193129826941270:ℤ)) (.leaf (2251519290630473:ℤ))) (.branch 146 (.leaf (2281505435689720:ℤ)) (.leaf (2312035518768687:ℤ))))) (.branch 156 (.branch 152 (.branch 150 (.leaf (2343122223707357:ℤ)) (.leaf (2374778598148677:ℤ))) (.branch 154 (.leaf (2407018065967130:ℤ)) (.leaf (2439854440191279:ℤ)))) (.branch 160 (.branch 158 (.leaf (2473301936442487:ℤ)) (.leaf (2507375186913476:ℤ))) (.branch 162 (.leaf (2542089254911362:ℤ)) (.branch 164 (.leaf (2577459649991557:ℤ)) (.leaf (2613502343709364:ℤ))))))) (.branch 183 (.branch 174 (.branch 170 (.branch 168 (.leaf (2650233786018748:ℤ)) (.leaf (2687670922348092:ℤ))) (.branch 172 (.leaf (2725831211385207:ℤ)) (.leaf (2764732643605099:ℤ)))) (.branch 179 (.branch 177 (.leaf (2804393760576163:ℤ)) (.leaf (2865351815490271:ℤ))) (.branch 180 (.leaf (2906997064140897:ℤ)) (.branch 182 (.leaf (2928129330660626:ℤ)) (.leaf (2971026346691681:ℤ)))))) (.branch 191 (.branch 187 (.branch 185 (.leaf (2992796499964092:ℤ)) (.leaf (3036993926536869:ℤ))) (.branch 189 (.leaf (3082086465461078:ℤ)) (.leaf (3128097496074039:ℤ)))) (.branch 195 (.branch 193 (.leaf (3175051150188356:ℤ)) (.leaf (3222972340975084:ℤ))) (.branch 197 (.leaf (3271886793137776:ℤ)) (.branch 200 (.leaf (3321821074442900:ℤ)) (.leaf (3398694957310621:ℤ)))))))), (.branch 166 (.branch 148 (.branch 138 (.branch 130 (.branch 122 (.leaf (1855983998385017:ℤ)) (.leaf (1974850116543036:ℤ))) (.branch 134 (.leaf (2077471088189938:ℤ)) (.leaf (2131501046709361:ℤ)))) (.branch 144 (.branch 142 (.leaf (2187455288028724:ℤ)) (.leaf (2245423287643090:ℤ))) (.branch 146 (.leaf (2275191819924615:ℤ)) (.leaf (2305499720789942:ℤ))))) (.branch 156 (.branch 152 (.branch 150 (.leaf (2336359696991905:ℤ)) (.leaf (2367784827531418:ℤ))) (.branch 154 (.leaf (2399788576760847:ℤ)) (.leaf (2432384808027581:ℤ)))) (.branch 160 (.branch 158 (.leaf (2465587797883213:ℤ)) (.leaf (2499412250885592:ℤ))) (.branch 162 (.leaf (2533873315021848:ℤ)) (.branch 164 (.leaf (2568986597782521:ℤ)) (.leaf (2604768182918129:ℤ))))))) (.branch 183 (.branch 174 (.branch 170 (.branch 168 (.leaf (2641234647911807:ℤ)) (.leaf (2678403082202915:ℤ))) (.branch 172 (.leaf (2716291106198739:ℤ)) (.leaf (2754916891113382:ℤ)))) (.branch 179 (.branch 177 (.leaf (2794299179675553:ℤ)) (.leaf (2854833521779783:ℤ))) (.branch 180 (.leaf (2896193017154955:ℤ)) (.branch 182 (.leaf (2917181528029697:ℤ)) (.leaf (2959789465932028:ℤ)))))) (.branch 191 (.branch 187 (.branch 185 (.leaf (2981414378669253:ℤ)) (.leaf (3025320140582396:ℤ))) (.branch 189 (.leaf (3070119753016268:ℤ)) (.leaf (3115837005281672:ℤ)))) (.branch 195 (.branch 193 (.leaf (3162496476183559:ℤ)) (.leaf (3210123565558185:ℤ))) (.branch 197 (.leaf (3258744527287606:ℤ)) (.branch 200 (.leaf (3308386503871072:ℤ)) (.leaf (3384825531063426:ℤ)))))))), (.branch 166 (.branch 148 (.branch 138 (.branch 130 (.branch 122 (.leaf (1863744271926317:ℤ)) (.leaf (1984818916537486:ℤ))) (.branch 134 (.leaf (2089548167193750:ℤ)) (.leaf (2144761457247924:ℤ)))) (.branch 144 (.branch 142 (.leaf (2201993543907434:ℤ)) (.leaf (2261340798384412:ℤ))) (.branch 146 (.leaf (2291839286591678:ℤ)) (.leaf (2322905326461763:ℤ))))) (.branch 156 (.branch 152 (.branch 150 (.leaf (2354552644688197:ℤ)) (.leaf (2386795379636489:ℤ))) (.branch 154 (.leaf (2419648096137298:ℤ)) (.leaf (2453125800900716:ℤ)))) (.branch 160 (.branch 158 (.leaf (2487243958581294:ℤ)) (.leaf (2522018508525816:ℤ))) (.branch 162 (.leaf (2557465882236551:ℤ)) (.branch 164 (.leaf (2593603021585436:ℤ)) (.leaf (2630447397815832:ℤ))))))) (.branch 183 (.branch 174 (.branch 170 (.branch 168 (.leaf (2668017031371276:ℤ)) (.leaf (2706330512592309:ℤ))) (.branch 172 (.leaf (2745407023324926:ℤ)) (.leaf (2785266359486595:ℤ)))) (.branch 179 (.branch 177 (.leaf (2825928954638984:ℤ)) (.leaf (2888475292518853:ℤ))) (.branch 180 (.leaf (2931239841794631:ℤ)) (.branch 182 (.leaf (2952950719400847:ℤ)) (.leaf (2997044324844050:ℤ)))))) (.branch 191 (.branch 187 (.branch 185 (.leaf (3019433055792123:ℤ)) (.leaf (3064909756951430:ℤ))) (.branch 189 (.leaf (3111339889586092:ℤ)) (.leaf (3158749537271662:ℤ)))) (.branch 195 (.branch 193 (.leaf (3207165670359634:ℤ)) (.leaf (3256616182154092:ℤ))) (.branch 197 (.leaf (3307129926814618:ℤ)) (.branch 200 (.leaf (3358736759080284:ℤ)) (.leaf (3438264429533284:ℤ))))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 15 14) 8000 (endpointMeanRuns 15 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 15 14, EndpointRunConditions (endpointMeanCutoff 15 14) (endpointMeanBox 15 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 15 14 h) (endpointMeanCornerA 15 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 14, endpointJoint24Q (endpointMeanCornerK 15 14 h) (endpointMeanCornerA 15 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 15 14, endpointRunWeightQ (endpointMeanCutoff 15 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 15 14) = (55217229/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 15 14 h = (logRoundedQ ((endpointMeanCutoff 15 14:ℚ)/200)).2+(55217229/125000000000000:ℚ)+((endpointMeanRuns 15 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 15 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 15 14) r*endpointJoint24Q (endpointMeanCornerK 15 14 h) (endpointMeanCornerA 15 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 15 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 15 14 h≤endpointMeanCorner 15 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 15 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint15_14

namespace EndpointAnalyticJoint15_15
private noncomputable def weights : IntegerLookupTree := (.branch 1517 (.branch 1243 (.branch 1109 (.branch 1064 (.branch 1032 (.leaf (96112360800000:ℤ)) (.leaf (1604657600000:ℤ))) (.branch 1086 (.leaf (1033641700000:ℤ)) (.leaf (1034975500000:ℤ)))) (.branch 1159 (.branch 1134 (.leaf (1072606900000:ℤ)) (.leaf (1020322900000:ℤ))) (.branch 1186 (.leaf (1046090000000:ℤ)) (.branch 1214 (.leaf (1025616500000:ℤ)) (.leaf (1002429700000:ℤ)))))) (.branch 1340 (.branch 1289 (.branch 1258 (.leaf (488069300000:ℤ)) (.leaf (977781200000:ℤ))) (.branch 1306 (.leaf (501757100000:ℤ)) (.leaf (966521400000:ℤ)))) (.branch 1394 (.branch 1375 (.leaf (925986700000:ℤ)) (.leaf (466701600000:ℤ))) (.branch 1433 (.leaf (916183500000:ℤ)) (.branch 1474 (.leaf (884071700000:ℤ)) (.leaf (847400600000:ℤ))))))) (.branch 2063 (.branch 1719 (.branch 1612 (.branch 1563 (.leaf (823621900000:ℤ)) (.leaf (791114100000:ℤ))) (.branch 1664 (.leaf (751635700000:ℤ)) (.leaf (706941300000:ℤ)))) (.branch 1842 (.branch 1778 (.leaf (668868300000:ℤ)) (.leaf (632704200000:ℤ))) (.branch 1910 (.leaf (579851000000:ℤ)) (.branch 1983 (.leaf (531480600000:ℤ)) (.leaf (489972100000:ℤ)))))) (.branch 2456 (.branch 2242 (.branch 2149 (.leaf (436045200000:ℤ)) (.leaf (384541900000:ℤ))) (.branch 2344 (.leaf (337407600000:ℤ)) (.leaf (289570200000:ℤ)))) (.branch 3033 (.branch 2714 (.leaf (471982500000:ℤ)) (.leaf (303057800000:ℤ))) (.branch 3438 (.leaf (168770900000:ℤ)) (.branch 4687 (.leaf (135128100000:ℤ)) (.leaf (11861500000:ℤ))))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 168 (.branch 150 (.branch 138 (.branch 130 (.branch 122 (.leaf (1859360237688077:ℤ)) (.leaf (1979021463559056:ℤ))) (.branch 134 (.leaf (2082357742559222:ℤ)) (.leaf (2136772489858315:ℤ)))) (.branch 144 (.branch 142 (.leaf (2193129826941270:ℤ)) (.leaf (2251519290630473:ℤ))) (.branch 146 (.leaf (2281505435689720:ℤ)) (.branch 148 (.leaf (2312035518768687:ℤ)) (.leaf (2343122223707357:ℤ)))))) (.branch 158 (.branch 154 (.branch 152 (.leaf (2374778598148677:ℤ)) (.leaf (2407018065967130:ℤ))) (.branch 156 (.leaf (2439854440191279:ℤ)) (.leaf (2473301936442487:ℤ)))) (.branch 162 (.branch 160 (.leaf (2507375186913476:ℤ)) (.leaf (2542089254911362:ℤ))) (.branch 164 (.leaf (2577459649991557:ℤ)) (.branch 166 (.leaf (2613502343709364:ℤ)) (.leaf (2650233786018748:ℤ))))))) (.branch 183 (.branch 175 (.branch 172 (.branch 170 (.leaf (2687670922348092:ℤ)) (.leaf (2725831211385207:ℤ))) (.branch 174 (.leaf (2764732643605099:ℤ)) (.leaf (2804393760576163:ℤ)))) (.branch 179 (.branch 177 (.leaf (2824515150707532:ℤ)) (.leaf (2865351815490271:ℤ))) (.branch 180 (.leaf (2906997064140897:ℤ)) (.branch 182 (.leaf (2928129330660626:ℤ)) (.leaf (2971026346691681:ℤ)))))) (.branch 191 (.branch 187 (.branch 185 (.leaf (2992796499964092:ℤ)) (.leaf (3036993926536869:ℤ))) (.branch 189 (.leaf (3082086465461078:ℤ)) (.leaf (3128097496074039:ℤ)))) (.branch 195 (.branch 193 (.leaf (3175051150188356:ℤ)) (.leaf (3222972340975084:ℤ))) (.branch 197 (.leaf (3271886793137776:ℤ)) (.branch 200 (.leaf (3321821074442900:ℤ)) (.leaf (3398694957310621:ℤ)))))))), (.branch 168 (.branch 150 (.branch 138 (.branch 130 (.branch 122 (.leaf (1866841505499748:ℤ)) (.leaf (1988623477824807:ℤ))) (.branch 134 (.leaf (2093981966905484:ℤ)) (.leaf (2149530849566237:ℤ)))) (.branch 144 (.branch 142 (.leaf (2207112233747653:ℤ)) (.leaf (2266822135907324:ℤ))) (.branch 146 (.leaf (2297506805743632:ℤ)) (.branch 148 (.leaf (2328762167237693:ℤ)) (.leaf (2360601859845874:ℤ)))))) (.branch 158 (.branch 154 (.branch 152 (.leaf (2393039923079246:ℤ)) (.leaf (2426090810446790:ℤ))) (.branch 156 (.leaf (2459769403962844:ℤ)) (.leaf (2494091029244521:ℤ)))) (.branch 162 (.branch 160 (.leaf (2529071471226622:ℤ)) (.leaf (2564726990522707:ℤ))) (.branch 164 (.leaf (2601074340462921:ℤ)) (.branch 166 (.leaf (2638130784839972:ℤ)) (.leaf (2675914116397493:ℤ))))))) (.branch 183 (.branch 175 (.branch 172 (.branch 170 (.leaf (2714442676095510:ℤ)) (.leaf (2753735373190896:ℤ))) (.branch 174 (.leaf (2793811706171640:ℤ)) (.leaf (2834691784586789:ℤ)))) (.branch 179 (.branch 177 (.leaf (2855439685236627:ℤ)) (.leaf (2897564480178031:ℤ))) (.branch 180 (.leaf (2940546119675774:ℤ)) (.branch 182 (.leaf (2962365238936228:ℤ)) (.leaf (3006674433744168:ℤ)))))) (.branch 191 (.branch 187 (.branch 185 (.leaf (3029170390560564:ℤ)) (.leaf (3074860082675406:ℤ))) (.branch 189 (.leaf (3121500797235636:ℤ)) (.leaf (3169118025406654:ℤ)))) (.branch 195 (.branch 193 (.leaf (3217738097984490:ℤ)) (.leaf (3267388218292614:ℤ))) (.branch 197 (.leaf (3318096496576109:ℤ)) (.branch 200 (.leaf (3369891985970638:ℤ)) (.leaf (3449689717273837:ℤ)))))))), (.branch 168 (.branch 150 (.branch 138 (.branch 130 (.branch 122 (.leaf (1863744271926317:ℤ)) (.leaf (1984818916537486:ℤ))) (.branch 134 (.leaf (2089548167193750:ℤ)) (.leaf (2144761457247924:ℤ)))) (.branch 144 (.branch 142 (.leaf (2201993543907434:ℤ)) (.leaf (2261340798384412:ℤ))) (.branch 146 (.leaf (2291839286591678:ℤ)) (.branch 148 (.leaf (2322905326461763:ℤ)) (.leaf (2354552644688197:ℤ)))))) (.branch 158 (.branch 154 (.branch 152 (.leaf (2386795379636489:ℤ)) (.leaf (2419648096137298:ℤ))) (.branch 156 (.leaf (2453125800900716:ℤ)) (.leaf (2487243958581294:ℤ)))) (.branch 162 (.branch 160 (.leaf (2522018508525816:ℤ)) (.leaf (2557465882236551:ℤ))) (.branch 164 (.leaf (2593603021585436:ℤ)) (.branch 166 (.leaf (2630447397815832:ℤ)) (.leaf (2668017031371276:ℤ))))))) (.branch 183 (.branch 175 (.branch 172 (.branch 170 (.leaf (2706330512592309:ℤ)) (.leaf (2745407023324926:ℤ))) (.branch 174 (.leaf (2785266359486595:ℤ)) (.leaf (2825928954638984:ℤ)))) (.branch 179 (.branch 177 (.leaf (2846568040219340:ℤ)) (.leaf (2888475292518853:ℤ))) (.branch 180 (.leaf (2931239841794631:ℤ)) (.branch 182 (.leaf (2952950719400847:ℤ)) (.leaf (2997044324844050:ℤ)))))) (.branch 191 (.branch 187 (.branch 185 (.leaf (3019433055792123:ℤ)) (.leaf (3064909756951430:ℤ))) (.branch 189 (.leaf (3111339889586092:ℤ)) (.leaf (3158749537271662:ℤ)))) (.branch 195 (.branch 193 (.leaf (3207165670359634:ℤ)) (.leaf (3256616182154092:ℤ))) (.branch 197 (.leaf (3307129926814618:ℤ)) (.branch 200 (.leaf (3358736759080284:ℤ)) (.leaf (3438264429533284:ℤ)))))))), (.branch 168 (.branch 150 (.branch 138 (.branch 130 (.branch 122 (.leaf (1871536992862357:ℤ)) (.leaf (1994838037805688:ℤ))) (.branch 134 (.leaf (2101695454557186:ℤ)) (.leaf (2158104362931365:ℤ)))) (.branch 144 (.branch 142 (.leaf (2216628423879513:ℤ)) (.leaf (2277371146268554:ℤ))) (.branch 146 (.leaf (2308608561953729:ℤ)) (.branch 148 (.leaf (2340442337531766:ℤ)) (.leaf (2372887258646882:ℤ)))))) (.branch 158 (.branch 154 (.branch 152 (.leaf (2405958564314894:ℤ)) (.leaf (2439671963537441:ℤ))) (.branch 156 (.leaf (2474043652626091:ℤ)) (.leaf (2509090333270775:ℤ)))) (.branch 162 (.branch 160 (.leaf (2544829231389537:ℤ)) (.leaf (2581278116797871:ℤ))) (.branch 164 (.leaf (2618455323738739:ℤ)) (.branch 166 (.leaf (2656379772316022:ℤ)) (.leaf (2695070990877317:ℤ))))))) (.branch 183 (.branch 175 (.branch 172 (.branch 170 (.leaf (2734549139393980:ℤ)) (.leaf (2774835033889174:ℤ))) (.branch 174 (.leaf (2815950171967789:ℤ)) (.leaf (2857916759505409:ℤ)))) (.branch 179 (.branch 177 (.leaf (2879226486667102:ℤ)) (.leaf (2922513502745486:ℤ))) (.branch 180 (.leaf (2966710767973823:ℤ)) (.branch 182 (.leaf (2989158496797267:ℤ)) (.leaf (3034768110525538:ℤ)))))) (.branch 191 (.branch 187 (.branch 185 (.leaf (3057936543017378:ℤ)) (.leaf (3105017446665240:ℤ))) (.branch 189 (.leaf (3153113457225560:ℤ)) (.leaf (3202253077519999:ℤ)))) (.branch 195 (.branch 193 (.leaf (3252465801810546:ℤ)) (.leaf (3303782157065891:ℤ))) (.branch 197 (.leaf (3356233746232423:ℤ)) (.branch 200 (.leaf (3409853293621327:ℤ)) (.leaf (3492547009854233:ℤ))))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 15 15) 8000 (endpointMeanRuns 15 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 15 15, EndpointRunConditions (endpointMeanCutoff 15 15) (endpointMeanBox 15 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 15 15 h) (endpointMeanCornerA 15 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 15, endpointJoint24Q (endpointMeanCornerK 15 15 h) (endpointMeanCornerA 15 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 15 15, endpointRunWeightQ (endpointMeanCutoff 15 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 15 15) = (220174039/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 15 15 h = (logRoundedQ ((endpointMeanCutoff 15 15:ℚ)/200)).2+(220174039/500000000000000:ℚ)+((endpointMeanRuns 15 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 15 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 15 15) r*endpointJoint24Q (endpointMeanCornerK 15 15 h) (endpointMeanCornerA 15 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 15 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 15 15 h≤endpointMeanCorner 15 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 15 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint15_15

namespace EndpointAnalyticJoint15_16
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1186 (.branch 1086 (.branch 1032 (.leaf (92789274700000:ℤ)) (.branch 1064 (.leaf (1593649100000:ℤ)) (.leaf (1026654000000:ℤ)))) (.branch 1134 (.branch 1109 (.leaf (1028060000000:ℤ)) (.leaf (1065525600000:ℤ))) (.branch 1159 (.leaf (1013668000000:ℤ)) (.leaf (1039349700000:ℤ))))) (.branch 1306 (.branch 1214 (.leaf (1019089800000:ℤ)) (.branch 1258 (.leaf (1512143100000:ℤ)) (.leaf (1501802200000:ℤ)))) (.branch 1394 (.branch 1340 (.leaf (960675000000:ℤ)) (.leaf (1416111200000:ℤ))) (.branch 1433 (.leaf (910821400000:ℤ)) (.leaf (878967400000:ℤ)))))) (.branch 2063 (.branch 1612 (.branch 1517 (.leaf (842574600000:ℤ)) (.branch 1563 (.leaf (818996000000:ℤ)) (.leaf (786733300000:ℤ)))) (.branch 1778 (.branch 1664 (.leaf (747533200000:ℤ)) (.leaf (1430435500000:ℤ))) (.branch 1910 (.leaf (1265808300000:ℤ)) (.leaf (1070298600000:ℤ))))) (.branch 2714 (.branch 2242 (.leaf (864705700000:ℤ)) (.branch 2456 (.leaf (664752800000:ℤ)) (.leaf (469845600000:ℤ)))) (.branch 3438 (.branch 3033 (.leaf (301737500000:ℤ)) (.leaf (168065300000:ℤ))) (.branch 4687 (.leaf (134592400000:ℤ)) (.leaf (11818700000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 170 (.branch 150 (.branch 134 (.branch 122 (.leaf (1866841505499748:ℤ)) (.branch 130 (.leaf (1988623477824807:ℤ)) (.leaf (2093981966905484:ℤ)))) (.branch 142 (.branch 138 (.leaf (2149530849566237:ℤ)) (.leaf (2207112233747653:ℤ))) (.branch 146 (.leaf (2266822135907324:ℤ)) (.leaf (2328762167237693:ℤ))))) (.branch 162 (.branch 154 (.leaf (2393039923079246:ℤ)) (.branch 158 (.leaf (2459769403962844:ℤ)) (.leaf (2529071471226622:ℤ)))) (.branch 166 (.branch 164 (.leaf (2601074340462921:ℤ)) (.leaf (2638130784839972:ℤ))) (.branch 168 (.leaf (2675914116397493:ℤ)) (.leaf (2714442676095510:ℤ)))))) (.branch 187 (.branch 177 (.branch 172 (.leaf (2753735373190896:ℤ)) (.branch 174 (.leaf (2793811706171640:ℤ)) (.leaf (2834691784586789:ℤ)))) (.branch 182 (.branch 179 (.leaf (2897564480178031:ℤ)) (.leaf (2940546119675774:ℤ))) (.branch 185 (.leaf (3006674433744168:ℤ)) (.leaf (3074860082675406:ℤ))))) (.branch 193 (.branch 189 (.leaf (3121500797235636:ℤ)) (.branch 191 (.leaf (3169118025406654:ℤ)) (.leaf (3217738097984490:ℤ)))) (.branch 197 (.branch 195 (.leaf (3267388218292614:ℤ)) (.leaf (3318096496576109:ℤ))) (.branch 200 (.leaf (3369891985970638:ℤ)) (.leaf (3449689717273837:ℤ))))))), (.branch 170 (.branch 150 (.branch 134 (.branch 122 (.leaf (1874352874723144:ℤ)) (.branch 130 (.leaf (1998272080103707:ℤ)) (.leaf (2105671080482294:ℤ)))) (.branch 142 (.branch 138 (.leaf (2162365387595999:ℤ)) (.leaf (2221183786074613:ℤ))) (.branch 146 (.leaf (2282228989652833:ℤ)) (.leaf (2345609826290978:ℤ))))) (.branch 162 (.branch 154 (.leaf (2411441672042807:ℤ)) (.branch 158 (.leaf (2479846920784909:ℤ)) (.leaf (2550955493200834:ℤ)))) (.branch 166 (.branch 164 (.leaf (2624905388775640:ℤ)) (.leaf (2662991313044844:ℤ))) (.branch 168 (.leaf (2701843284962450:ℤ)) (.leaf (2741481101924230:ℤ)))))) (.branch 187 (.branch 177 (.branch 172 (.leaf (2781925188137114:ℤ)) (.branch 174 (.leaf (2823196618159710:ℤ)) (.leaf (2865317141467656:ℤ)))) (.branch 182 (.branch 179 (.leaf (2930139283909481:ℤ)) (.leaf (2974482357964006:ℤ))) (.branch 185 (.leaf (3042750247098007:ℤ)) (.leaf (3113198365467930:ℤ))))) (.branch 193 (.branch 189 (.leaf (3161419167286427:ℤ)) (.branch 191 (.leaf (3210676480372609:ℤ)) (.leaf (3260998950081996:ℤ)))) (.branch 197 (.branch 195 (.leaf (3312416192131368:ℤ)) (.leaf (3364958831608036:ℤ))) (.branch 200 (.leaf (3418658543796993:ℤ)) (.leaf (3501449613731027:ℤ))))))), (.branch 170 (.branch 150 (.branch 134 (.branch 122 (.leaf (1871536992862357:ℤ)) (.branch 130 (.leaf (1994838037805688:ℤ)) (.leaf (2101695454557186:ℤ)))) (.branch 142 (.branch 138 (.leaf (2158104362931365:ℤ)) (.leaf (2216628423879513:ℤ))) (.branch 146 (.leaf (2277371146268554:ℤ)) (.leaf (2340442337531766:ℤ))))) (.branch 162 (.branch 154 (.leaf (2405958564314894:ℤ)) (.branch 158 (.leaf (2474043652626091:ℤ)) (.leaf (2544829231389537:ℤ)))) (.branch 166 (.branch 164 (.leaf (2618455323738739:ℤ)) (.leaf (2656379772316022:ℤ))) (.branch 168 (.leaf (2695070990877317:ℤ)) (.leaf (2734549139393980:ℤ)))))) (.branch 187 (.branch 177 (.branch 172 (.leaf (2774835033889174:ℤ)) (.branch 174 (.leaf (2815950171967789:ℤ)) (.leaf (2857916759505409:ℤ)))) (.branch 182 (.branch 179 (.leaf (2922513502745486:ℤ)) (.leaf (2966710767973823:ℤ))) (.branch 185 (.leaf (3034768110525538:ℤ)) (.leaf (3105017446665240:ℤ))))) (.branch 193 (.branch 189 (.leaf (3153113457225560:ℤ)) (.branch 191 (.leaf (3202253077519999:ℤ)) (.leaf (3252465801810546:ℤ)))) (.branch 197 (.branch 195 (.leaf (3303782157065891:ℤ)) (.leaf (3356233746232423:ℤ))) (.branch 200 (.leaf (3409853293621327:ℤ)) (.leaf (3492547009854233:ℤ))))))), (.branch 170 (.branch 150 (.branch 134 (.branch 122 (.leaf (1879362296862773:ℤ)) (.branch 130 (.leaf (2004907734363229:ℤ)) (.leaf (2113913358426431:ℤ)))) (.branch 142 (.branch 138 (.leaf (2171530276975233:ℤ)) (.leaf (2231360570127590:ℤ))) (.branch 146 (.leaf (2293515131183199:ℤ)) (.leaf (2358111746058417:ℤ))))) (.branch 162 (.branch 154 (.leaf (2425275607028284:ℤ)) (.branch 158 (.leaf (2495139871282608:ℤ)) (.leaf (2567846268788945:ℤ)))) (.branch 166 (.branch 164 (.leaf (2643545764464975:ℤ)) (.leaf (2682567802203112:ℤ))) (.branch 168 (.leaf (2722399280238216:ℤ)) (.leaf (2763061998882624:ℤ)))))) (.branch 187 (.branch 177 (.branch 172 (.leaf (2804578483220209:ℤ)) (.branch 174 (.leaf (2846972011849908:ℤ)) (.leaf (2890266646956569:ℤ)))) (.branch 182 (.branch 179 (.leaf (2956952824159889:ℤ)) (.leaf (3002610927744236:ℤ))) (.branch 185 (.leaf (3072966725355983:ℤ)) (.leaf (3145649989279051:ℤ))))) (.branch 193 (.branch 189 (.leaf (3195447886427968:ℤ)) (.branch 191 (.leaf (3246355765624732:ℤ)) (.leaf (3298405782312106:ℤ)))) (.branch 197 (.branch 195 (.leaf (3351631242625353:ℤ)) (.leaf (3406066652542716:ℤ))) (.branch 200 (.leaf (3461747769481060:ℤ)) (.leaf (3547686591894127:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 15 16) 8000 (endpointMeanRuns 15 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 15 16, EndpointRunConditions (endpointMeanCutoff 15 16) (endpointMeanBox 15 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 15 16 h) (endpointMeanCornerA 15 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 16, endpointJoint24Q (endpointMeanCornerK 15 16 h) (endpointMeanCornerA 15 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 15 16, endpointRunWeightQ (endpointMeanCutoff 15 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 15 16) = (438974901/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 15 16 h = (logRoundedQ ((endpointMeanCutoff 15 16:ℚ)/200)).2+(438974901/1000000000000000:ℚ)+((endpointMeanRuns 15 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 15 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 15 16) r*endpointJoint24Q (endpointMeanCornerK 15 16 h) (endpointMeanCornerA 15 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 15 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 15 16 h≤endpointMeanCorner 15 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 15 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint15_16

namespace EndpointAnalyticJoint15_17
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1186 (.branch 1064 (.branch 1032 (.leaf (90104642300000:ℤ)) (.leaf (1584574600000:ℤ))) (.branch 1134 (.leaf (3276069000000:ℤ)) (.leaf (2101316200000:ℤ)))) (.branch 1340 (.branch 1258 (.leaf (2613290200000:ℤ)) (.leaf (2548728000000:ℤ))) (.branch 1394 (.leaf (1409122100000:ℤ)) (.leaf (1847442300000:ℤ))))) (.branch 1910 (.branch 1664 (.branch 1563 (.leaf (1718800300000:ℤ)) (.leaf (1591881600000:ℤ))) (.branch 1778 (.leaf (1424102300000:ℤ)) (.leaf (1260371700000:ℤ)))) (.branch 2242 (.branch 2063 (.leaf (1065845200000:ℤ)) (.leaf (861224700000:ℤ))) (.branch 2714 (.leaf (1304440200000:ℤ)) (.branch 3438 (.leaf (567106300000:ℤ)) (.leaf (354477000000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 150 (.branch 138 (.branch 130 (.leaf (1874352874723144:ℤ)) (.leaf (2105671080482294:ℤ))) (.branch 146 (.leaf (2221183786074613:ℤ)) (.leaf (2345609826290978:ℤ)))) (.branch 158 (.branch 154 (.leaf (2411441672042807:ℤ)) (.leaf (2479846920784909:ℤ))) (.branch 162 (.leaf (2550955493200834:ℤ)) (.leaf (2624905388775640:ℤ))))) (.branch 182 (.branch 174 (.branch 170 (.leaf (2701843284962450:ℤ)) (.leaf (2781925188137114:ℤ))) (.branch 177 (.leaf (2865317141467656:ℤ)) (.leaf (2930139283909481:ℤ)))) (.branch 191 (.branch 187 (.leaf (3042750247098007:ℤ)) (.leaf (3161419167286427:ℤ))) (.branch 197 (.leaf (3260998950081996:ℤ)) (.branch 200 (.leaf (3418658543796993:ℤ)) (.leaf (3501449613731027:ℤ))))))), (.branch 166 (.branch 150 (.branch 138 (.branch 130 (.leaf (1881894466473437:ℤ)) (.leaf (2117425445517035:ℤ))) (.branch 146 (.leaf (2235345052273776:ℤ)) (.leaf (2362579371391525:ℤ)))) (.branch 158 (.branch 154 (.leaf (2429984924857457:ℤ)) (.leaf (2500088317473553:ℤ))) (.branch 162 (.leaf (2573028877327602:ℤ)) (.leaf (2648954777200691:ℤ))))) (.branch 182 (.branch 174 (.branch 170 (.leaf (2728023702914804:ℤ)) (.leaf (2810403580437003:ℤ))) (.branch 177 (.leaf (2896273367647684:ℤ)) (.leaf (2963080297899710:ℤ)))) (.branch 191 (.branch 187 (.leaf (3079258918859972:ℤ)) (.leaf (3201848021354688:ℤ))) (.branch 197 (.leaf (3304841422332285:ℤ)) (.branch 200 (.leaf (3468130814795199:ℤ)) (.leaf (3553986126956918:ℤ))))))), (.branch 166 (.branch 150 (.branch 138 (.branch 130 (.leaf (1879362296862773:ℤ)) (.leaf (2113913358426431:ℤ))) (.branch 146 (.leaf (2231360570127590:ℤ)) (.leaf (2358111746058417:ℤ)))) (.branch 158 (.branch 154 (.leaf (2425275607028284:ℤ)) (.leaf (2495139871282608:ℤ))) (.branch 162 (.leaf (2567846268788945:ℤ)) (.leaf (2643545764464975:ℤ))))) (.branch 182 (.branch 174 (.branch 170 (.leaf (2722399280238216:ℤ)) (.leaf (2804578483220209:ℤ))) (.branch 177 (.leaf (2890266646956569:ℤ)) (.leaf (2956952824159889:ℤ)))) (.branch 191 (.branch 187 (.leaf (3072966725355983:ℤ)) (.leaf (3195447886427968:ℤ))) (.branch 197 (.leaf (3298405782312106:ℤ)) (.branch 200 (.leaf (3461747769481060:ℤ)) (.leaf (3547686591894127:ℤ))))))), (.branch 166 (.branch 150 (.branch 138 (.branch 130 (.leaf (1887220320164453:ℤ)) (.leaf (2126202289320379:ℤ))) (.branch 146 (.leaf (2246190629102375:ℤ)) (.leaf (2375914551589844:ℤ)))) (.branch 158 (.branch 154 (.leaf (2444747743077334:ℤ)) (.leaf (2516415977808579:ℤ))) (.branch 162 (.leaf (2591071486762557:ℤ)) (.leaf (2668876625644495:ℤ))))) (.branch 182 (.branch 174 (.branch 170 (.leaf (2750004681186124:ℤ)) (.leaf (2834640752505332:ℤ))) (.branch 177 (.leaf (2922982715548111:ℤ)) (.leaf (2991797983514260:ℤ)))) (.branch 191 (.branch 187 (.leaf (3111646146008097:ℤ)) (.leaf (3238350707450152:ℤ))) (.branch 197 (.leaf (3344994649515970:ℤ)) (.branch 200 (.leaf (3514432026129834:ℤ)) (.leaf (3603696705812040:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 15 17) 8000 (endpointMeanRuns 15 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 15 17, EndpointRunConditions (endpointMeanCutoff 15 17) (endpointMeanBox 15 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 15 17 h) (endpointMeanCornerA 15 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 17, endpointJoint24Q (endpointMeanCornerK 15 17 h) (endpointMeanCornerA 15 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 15 17, endpointRunWeightQ (endpointMeanCutoff 15 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 15 17) = (437842969/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 15 17 h = (logRoundedQ ((endpointMeanCutoff 15 17:ℚ)/200)).2+(437842969/1000000000000000:ℚ)+((endpointMeanRuns 15 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 15 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 15 17) r*endpointJoint24Q (endpointMeanCornerK 15 17 h) (endpointMeanCornerA 15 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 15 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 15 17 h≤endpointMeanCorner 15 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 15 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint15_17

namespace EndpointAnalyticJoint15_18
private noncomputable def weights : IntegerLookupTree := (.branch 1664 (.branch 1134 (.branch 1032 (.leaf (86981263200000:ℤ)) (.leaf (5095582200000:ℤ))) (.branch 1258 (.leaf (5009922800000:ℤ)) (.branch 1474 (.leaf (6620587200000:ℤ)) (.leaf (3571982900000:ℤ))))) (.branch 2242 (.branch 1910 (.leaf (2935696000000:ℤ)) (.leaf (2149706500000:ℤ))) (.branch 2714 (.leaf (1298473300000:ℤ)) (.branch 3438 (.leaf (564698600000:ℤ)) (.leaf (353098100000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 138 (.branch 130 (.leaf (1881894466473437:ℤ)) (.leaf (2117425445517035:ℤ))) (.branch 146 (.leaf (2235345052273776:ℤ)) (.branch 154 (.leaf (2362579371391525:ℤ)) (.leaf (2500088317473553:ℤ))))) (.branch 182 (.branch 170 (.leaf (2648954777200691:ℤ)) (.leaf (2810403580437003:ℤ))) (.branch 191 (.leaf (3079258918859972:ℤ)) (.branch 200 (.leaf (3304841422332285:ℤ)) (.leaf (3553986126956918:ℤ)))))), (.branch 162 (.branch 138 (.branch 130 (.leaf (1889466402353109:ℤ)) (.leaf (2129245426259114:ℤ))) (.branch 146 (.leaf (2249596604320341:ℤ)) (.branch 154 (.leaf (2379671684335934:ℤ)) (.leaf (2520494931674808:ℤ))))) (.branch 182 (.branch 170 (.leaf (2673224506170624:ℤ)) (.leaf (2839173504238687:ℤ))) (.branch 191 (.leaf (3116205642714804:ℤ)) (.branch 200 (.leaf (3349273334322506:ℤ)) (.leaf (3607310909478788:ℤ)))))), (.branch 162 (.branch 138 (.branch 130 (.leaf (1887220320164453:ℤ)) (.leaf (2126202289320379:ℤ))) (.branch 146 (.leaf (2246190629102375:ℤ)) (.branch 154 (.leaf (2375914551589844:ℤ)) (.leaf (2516415977808579:ℤ))))) (.branch 182 (.branch 170 (.leaf (2668876625644495:ℤ)) (.leaf (2834640752505332:ℤ))) (.branch 191 (.leaf (3111646146008097:ℤ)) (.branch 200 (.leaf (3344994649515970:ℤ)) (.leaf (3603696705812040:ℤ)))))), (.branch 162 (.branch 138 (.branch 130 (.leaf (1895111199573927:ℤ)) (.leaf (2138562660144395:ℤ))) (.branch 146 (.leaf (2261119251551008:ℤ)) (.branch 154 (.leaf (2393851761220364:ℤ)) (.leaf (2537873506111384:ℤ))))) (.branch 182 (.branch 170 (.leaf (2694450211022976:ℤ)) (.leaf (2865025259174783:ℤ))) (.branch 191 (.leaf (3150812424382956:ℤ)) (.branch 200 (.leaf (3392241568727555:ℤ)) (.leaf (3660591095378273:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 15 18) 8000 (endpointMeanRuns 15 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 15 18, EndpointRunConditions (endpointMeanCutoff 15 18) (endpointMeanBox 15 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 15 18 h) (endpointMeanCornerA 15 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 15 18, endpointJoint24Q (endpointMeanCornerK 15 18 h) (endpointMeanCornerA 15 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 15 18, endpointRunWeightQ (endpointMeanCutoff 15 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 15 18) = (21824959/50000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 15 18 h = (logRoundedQ ((endpointMeanCutoff 15 18:ℚ)/200)).2+(21824959/50000000000000:ℚ)+((endpointMeanRuns 15 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 15 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 15 18) r*endpointJoint24Q (endpointMeanCornerK 15 18 h) (endpointMeanCornerA 15 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 15 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 15 18 h≤endpointMeanCorner 15 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 15 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint15_18

namespace EndpointAnalyticJoint16_03
private noncomputable def weights : IntegerLookupTree := (.branch 1521 (.branch 1004 (.leaf (137999818000000:ℤ)) (.leaf (32887782000000:ℤ))) (.branch 2181 (.leaf (11524152400000:ℤ)) (.leaf (10980151500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.leaf (1777501569762029:ℤ)) (.leaf (2132755794329742:ℤ))) (.branch 200 (.leaf (2379224345517852:ℤ)) (.leaf (2878003822714936:ℤ)))), (.branch 166 (.branch 146 (.leaf (1780136423259488:ℤ)) (.leaf (2138457952103168:ℤ))) (.branch 200 (.leaf (2387761070817592:ℤ)) (.leaf (2894052641941947:ℤ)))), (.branch 166 (.branch 146 (.leaf (1778549222896249:ℤ)) (.leaf (2135288368588965:ℤ))) (.branch 200 (.leaf (2383283615667892:ℤ)) (.leaf (2886631138336069:ℤ)))), (.branch 166 (.branch 146 (.leaf (1781287848462510:ℤ)) (.leaf (2141244774778693:ℤ))) (.branch 200 (.leaf (2392232042803016:ℤ)) (.leaf (2903574386813572:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 16 3) 8000 (endpointMeanRuns 16 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 16 3, EndpointRunConditions (endpointMeanCutoff 16 3) (endpointMeanBox 16 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 16 3 h) (endpointMeanCornerA 16 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 3, endpointJoint24Q (endpointMeanCornerK 16 3 h) (endpointMeanCornerA 16 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 16 3, endpointRunWeightQ (endpointMeanCutoff 16 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 16 3) = (456115123/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 16 3 h = (logRoundedQ ((endpointMeanCutoff 16 3:ℚ)/200)).2+(456115123/1000000000000000:ℚ)+((endpointMeanRuns 16 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 16 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 16 3) r*endpointJoint24Q (endpointMeanCornerK 16 3 h) (endpointMeanCornerA 16 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 16 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 16 3 h≤endpointMeanCorner 16 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 16 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint16_03

namespace EndpointAnalyticJoint16_04
private noncomputable def weights : IntegerLookupTree := (.branch 1521 (.branch 1004 (.leaf (134797651800000:ℤ)) (.leaf (32736516200000:ℤ))) (.branch 2181 (.leaf (11479803100000:ℤ)) (.leaf (10943720800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.leaf (1780136423259488:ℤ)) (.leaf (2138457952103168:ℤ))) (.branch 200 (.leaf (2387761070817592:ℤ)) (.leaf (2894052641941947:ℤ)))), (.branch 166 (.branch 146 (.leaf (1787579561560971:ℤ)) (.leaf (2154602458877311:ℤ))) (.branch 200 (.leaf (2411973206857372:ℤ)) (.leaf (2939743323449710:ℤ)))), (.branch 166 (.branch 146 (.leaf (1781287848462510:ℤ)) (.leaf (2141244774778693:ℤ))) (.branch 200 (.leaf (2392232042803016:ℤ)) (.leaf (2903574386813572:ℤ)))), (.branch 166 (.branch 146 (.leaf (1789024977851270:ℤ)) (.leaf (2158112858036351:ℤ))) (.branch 200 (.leaf (2417619912690180:ℤ)) (.leaf (2951838381746290:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 16 4) 8000 (endpointMeanRuns 16 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 16 4, EndpointRunConditions (endpointMeanCutoff 16 4) (endpointMeanBox 16 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 16 4 h) (endpointMeanCornerA 16 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 4, endpointJoint24Q (endpointMeanCornerK 16 4 h) (endpointMeanCornerA 16 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 16 4, endpointRunWeightQ (endpointMeanCutoff 16 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 16 4) = (227531911/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 16 4 h = (logRoundedQ ((endpointMeanCutoff 16 4:ℚ)/200)).2+(227531911/500000000000000:ℚ)+((endpointMeanRuns 16 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 16 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 16 4) r*endpointJoint24Q (endpointMeanCornerK 16 4 h) (endpointMeanCornerA 16 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 16 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 16 4 h≤endpointMeanCorner 16 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 16 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint16_04

namespace EndpointAnalyticJoint16_05
private noncomputable def weights : IntegerLookupTree := (.branch 1521 (.branch 1004 (.leaf (130897696900000:ℤ)) (.leaf (32549356200000:ℤ))) (.branch 2181 (.leaf (11424930000000:ℤ)) (.leaf (10898645400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.leaf (1787579561560971:ℤ)) (.leaf (2154602458877311:ℤ))) (.branch 200 (.leaf (2411973206857372:ℤ)) (.leaf (2939743323449710:ℤ)))), (.branch 166 (.branch 146 (.leaf (1795053821245655:ℤ)) (.leaf (2170868850254669:ℤ))) (.branch 200 (.leaf (2436430856377865:ℤ)) (.leaf (2986155359623377:ℤ)))), (.branch 166 (.branch 146 (.leaf (1789024977851270:ℤ)) (.leaf (2158112858036351:ℤ))) (.branch 200 (.leaf (2417619912690180:ℤ)) (.leaf (2951838381746290:ℤ)))), (.branch 166 (.branch 146 (.leaf (1796795713920293:ℤ)) (.leaf (2175113822987941:ℤ))) (.branch 200 (.leaf (2443277214608132:ℤ)) (.leaf (3000904633792675:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 16 5) 8000 (endpointMeanRuns 16 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 16 5, EndpointRunConditions (endpointMeanCutoff 16 5) (endpointMeanBox 16 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 16 5 h) (endpointMeanCornerA 16 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 5, endpointJoint24Q (endpointMeanCornerK 16 5 h) (endpointMeanCornerA 16 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 16 5, endpointRunWeightQ (endpointMeanCutoff 16 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 16 5) = (28360191/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 16 5 h = (logRoundedQ ((endpointMeanCutoff 16 5:ℚ)/200)).2+(28360191/62500000000000:ℚ)+((endpointMeanRuns 16 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 16 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 16 5) r*endpointJoint24Q (endpointMeanCornerK 16 5 h) (endpointMeanCornerA 16 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 16 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 16 5 h≤endpointMeanCorner 16 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 16 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint16_05

namespace EndpointAnalyticJoint16_06
private noncomputable def weights : IntegerLookupTree := (.branch 1255 (.branch 1004 (.leaf (126363857100000:ℤ)) (.leaf (15614410700000:ℤ))) (.branch 1521 (.leaf (9311406000000:ℤ)) (.branch 2181 (.leaf (11359890500000:ℤ)) (.leaf (10845218700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.leaf (1795053821245655:ℤ)) (.leaf (2170868850254669:ℤ))) (.branch 180 (.leaf (2436430856377865:ℤ)) (.branch 200 (.leaf (2646192900509418:ℤ)) (.leaf (2986155359623377:ℤ))))), (.branch 166 (.branch 146 (.leaf (1802559332438821:ℤ)) (.leaf (2187258046415505:ℤ))) (.branch 180 (.leaf (2461136508910317:ℤ)) (.branch 200 (.leaf (2678639349026197:ℤ)) (.leaf (3033300139055482:ℤ))))), (.branch 166 (.branch 146 (.leaf (1796795713920293:ℤ)) (.leaf (2175113822987941:ℤ))) (.branch 180 (.leaf (2443277214608132:ℤ)) (.branch 200 (.leaf (2655634711902725:ℤ)) (.leaf (3000904633792675:ℤ))))), (.branch 166 (.branch 146 (.leaf (1804600202642187:ℤ)) (.leaf (2192248716435533:ℤ))) (.branch 180 (.leaf (2469206807938913:ℤ)) (.branch 200 (.leaf (2689793174399744:ℤ)) (.leaf (3050786478286384:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 16 6) 8000 (endpointMeanRuns 16 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 16 6, EndpointRunConditions (endpointMeanCutoff 16 6) (endpointMeanBox 16 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 16 6 h) (endpointMeanCornerA 16 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 6, endpointJoint24Q (endpointMeanCornerK 16 6 h) (endpointMeanCornerA 16 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 16 6, endpointRunWeightQ (endpointMeanCutoff 16 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 16 6) = (113055323/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 16 6 h = (logRoundedQ ((endpointMeanCutoff 16 6:ℚ)/200)).2+(113055323/250000000000000:ℚ)+((endpointMeanRuns 16 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 16 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 16 6) r*endpointJoint24Q (endpointMeanCornerK 16 6 h) (endpointMeanCornerA 16 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 16 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 16 6 h≤endpointMeanCorner 16 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 16 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint16_06

namespace EndpointAnalyticJoint16_07
private noncomputable def weights : IntegerLookupTree := (.branch 1255 (.branch 1004 (.leaf (121983926700000:ℤ)) (.leaf (15505483900000:ℤ))) (.branch 1521 (.leaf (9252931900000:ℤ)) (.branch 2181 (.leaf (11295710500000:ℤ)) (.leaf (10792498200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.leaf (1802559332438821:ℤ)) (.leaf (2187258046415505:ℤ))) (.branch 180 (.leaf (2461136508910317:ℤ)) (.branch 200 (.leaf (2678639349026197:ℤ)) (.leaf (3033300139055482:ℤ))))), (.branch 166 (.branch 146 (.leaf (1810096225809841:ℤ)) (.leaf (2203770974487071:ℤ))) (.branch 180 (.leaf (2486092679230074:ℤ)) (.branch 200 (.leaf (2711483641563018:ℤ)) (.leaf (3081189230139201:ℤ))))), (.branch 166 (.branch 146 (.leaf (1804600202642187:ℤ)) (.leaf (2192248716435533:ℤ))) (.branch 180 (.leaf (2469206807938913:ℤ)) (.branch 200 (.leaf (2689793174399744:ℤ)) (.leaf (3050786478286384:ℤ))))), (.branch 166 (.branch 146 (.leaf (1812438590623603:ℤ)) (.leaf (2209518593427599:ℤ))) (.branch 180 (.leaf (2495411582410126:ℤ)) (.branch 200 (.leaf (2724391004764229:ℤ)) (.leaf (3101497472224587:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 16 7) 8000 (endpointMeanRuns 16 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 16 7, EndpointRunConditions (endpointMeanCutoff 16 7) (endpointMeanBox 16 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 16 7 h) (endpointMeanCornerA 16 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 7, endpointJoint24Q (endpointMeanCornerK 16 7 h) (endpointMeanCornerA 16 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 16 7, endpointRunWeightQ (endpointMeanCutoff 16 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 16 7) = (90139981/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 16 7 h = (logRoundedQ ((endpointMeanCutoff 16 7:ℚ)/200)).2+(90139981/200000000000000:ℚ)+((endpointMeanRuns 16 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 16 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 16 7) r*endpointJoint24Q (endpointMeanCornerK 16 7 h) (endpointMeanCornerA 16 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 16 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 16 7 h≤endpointMeanCorner 16 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 16 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint16_07

namespace EndpointAnalyticJoint16_08
private noncomputable def weights : IntegerLookupTree := (.branch 1521 (.branch 1004 (.leaf (117752332800000:ℤ)) (.branch 1255 (.leaf (15397978000000:ℤ)) (.leaf (9195220400000:ℤ)))) (.branch 2181 (.leaf (11232367600000:ℤ)) (.branch 3345 (.leaf (3356689400000:ℤ)) (.leaf (471196600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 130 (.leaf (1810096225809841:ℤ)) (.branch 146 (.leaf (2006460429053424:ℤ)) (.leaf (2203770974487071:ℤ)))) (.branch 180 (.leaf (2486092679230074:ℤ)) (.branch 200 (.leaf (2711483641563018:ℤ)) (.leaf (3081189230139201:ℤ))))), (.branch 166 (.branch 130 (.leaf (1817664632574433:ℤ)) (.branch 146 (.leaf (2018124697816276:ℤ)) (.leaf (2220408568596081:ℤ)))) (.branch 180 (.leaf (2511301907612545:ℤ)) (.branch 200 (.leaf (2744730656307527:ℤ)) (.leaf (3129834383907024:ℤ))))), (.branch 166 (.branch 130 (.leaf (1812438590623603:ℤ)) (.branch 146 (.leaf (2010283965303452:ℤ)) (.leaf (2209518593427599:ℤ)))) (.branch 180 (.leaf (2495411582410126:ℤ)) (.branch 200 (.leaf (2724391004764229:ℤ)) (.leaf (3101497472224587:ℤ))))), (.branch 166 (.branch 130 (.leaf (1820311025107977:ℤ)) (.branch 146 (.leaf (2022451697123652:ℤ)) (.leaf (2226924517323965:ℤ)))) (.branch 180 (.leaf (2521894458416970:ℤ)) (.branch 200 (.leaf (2759433854425119:ℤ)) (.leaf (3153051397952514:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 16 8) 8000 (endpointMeanRuns 16 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 16 8, EndpointRunConditions (endpointMeanCutoff 16 8) (endpointMeanBox 16 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 16 8 h) (endpointMeanCornerA 16 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 8, endpointJoint24Q (endpointMeanCornerK 16 8 h) (endpointMeanCornerA 16 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 16 8, endpointRunWeightQ (endpointMeanCutoff 16 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 16 8) = (449198363/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 16 8 h = (logRoundedQ ((endpointMeanCutoff 16 8:ℚ)/200)).2+(449198363/1000000000000000:ℚ)+((endpointMeanRuns 16 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 16 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 16 8) r*endpointJoint24Q (endpointMeanCornerK 16 8 h) (endpointMeanCornerA 16 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 16 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 16 8 h≤endpointMeanCorner 16 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 16 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint16_08

namespace EndpointAnalyticJoint16_09
private noncomputable def weights : IntegerLookupTree := (.branch 1521 (.branch 1004 (.leaf (113663729100000:ℤ)) (.branch 1255 (.leaf (15291856200000:ℤ)) (.leaf (9138252000000:ℤ)))) (.branch 2181 (.branch 1825 (.leaf (5565377400000:ℤ)) (.leaf (3110609900000:ℤ))) (.branch 3345 (.leaf (3340475500000:ℤ)) (.leaf (469223300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 130 (.leaf (1817664632574433:ℤ)) (.branch 146 (.leaf (2018124697816276:ℤ)) (.leaf (2220408568596081:ℤ)))) (.branch 180 (.branch 166 (.leaf (2345634905153138:ℤ)) (.leaf (2511301907612545:ℤ))) (.branch 200 (.leaf (2744730656307527:ℤ)) (.leaf (3129834383907024:ℤ))))), (.branch 155 (.branch 130 (.leaf (1825264684496968:ℤ)) (.branch 146 (.leaf (2029856775125863:ℤ)) (.leaf (2237171769921507:ℤ)))) (.branch 180 (.branch 166 (.leaf (2365935395196447:ℤ)) (.leaf (2536766760091799:ℤ))) (.branch 200 (.leaf (2778385331261558:ℤ)) (.leaf (3179247536914214:ℤ))))), (.branch 155 (.branch 130 (.leaf (1820311025107977:ℤ)) (.branch 146 (.leaf (2022451697123652:ℤ)) (.leaf (2226924517323965:ℤ)))) (.branch 180 (.branch 166 (.leaf (2353767677177240:ℤ)) (.leaf (2521894458416970:ℤ))) (.branch 200 (.leaf (2759433854425119:ℤ)) (.leaf (3153051397952514:ℤ))))), (.branch 155 (.branch 130 (.leaf (1828217653978324:ℤ)) (.branch 146 (.leaf (2034693077095159:ℤ)) (.leaf (2244467559861274:ℤ)))) (.branch 180 (.branch 166 (.leaf (2375051768813314:ℤ)) (.leaf (2548658387347724:ℤ))) (.branch 200 (.leaf (2794927447503603:ℤ)) (.leaf (3205462266909238:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 16 9) 8000 (endpointMeanRuns 16 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 16 9, EndpointRunConditions (endpointMeanCutoff 16 9) (endpointMeanBox 16 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 16 9 h) (endpointMeanCornerA 16 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 9, endpointJoint24Q (endpointMeanCornerK 16 9 h) (endpointMeanCornerA 16 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 16 9, endpointRunWeightQ (endpointMeanCutoff 16 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 16 9) = (223858077/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 16 9 h = (logRoundedQ ((endpointMeanCutoff 16 9:ℚ)/200)).2+(223858077/500000000000000:ℚ)+((endpointMeanRuns 16 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 16 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 16 9) r*endpointJoint24Q (endpointMeanCornerK 16 9 h) (endpointMeanCornerA 16 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 16 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 16 9 h≤endpointMeanCorner 16 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 16 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint16_09

namespace EndpointAnalyticJoint16_10
private noncomputable def weights : IntegerLookupTree := (.branch 1521 (.branch 1004 (.leaf (110362080400000:ℤ)) (.branch 1255 (.leaf (15204453400000:ℤ)) (.leaf (9091332400000:ℤ)))) (.branch 2181 (.branch 1825 (.leaf (5539173300000:ℤ)) (.leaf (3097041500000:ℤ))) (.branch 3345 (.leaf (3327121700000:ℤ)) (.leaf (467598000000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 130 (.leaf (1825264684496968:ℤ)) (.branch 146 (.leaf (2029856775125863:ℤ)) (.leaf (2237171769921507:ℤ)))) (.branch 180 (.branch 166 (.leaf (2365935395196447:ℤ)) (.leaf (2536766760091799:ℤ))) (.branch 200 (.leaf (2778385331261558:ℤ)) (.leaf (3179247536914214:ℤ))))), (.branch 155 (.branch 130 (.leaf (1832896513892746:ℤ)) (.branch 146 (.leaf (2041657055177402:ℤ)) (.leaf (2254061526747870:ℤ)))) (.branch 180 (.branch 166 (.leaf (2386411577499061:ℤ)) (.leaf (2562489828721738:ℤ))) (.branch 200 (.leaf (2812452664974528:ℤ)) (.leaf (3229440814167809:ℤ))))), (.branch 155 (.branch 130 (.leaf (1828217653978324:ℤ)) (.branch 146 (.leaf (2034693077095159:ℤ)) (.leaf (2244467559861274:ℤ)))) (.branch 180 (.branch 166 (.leaf (2375051768813314:ℤ)) (.leaf (2548658387347724:ℤ))) (.branch 200 (.leaf (2794927447503603:ℤ)) (.leaf (3205462266909238:ℤ))))), (.branch 155 (.branch 130 (.leaf (1836158625759979:ℤ)) (.branch 146 (.leaf (2047008550991292:ℤ)) (.leaf (2262148801219016:ℤ)))) (.branch 180 (.branch 166 (.leaf (2396528323181018:ℤ)) (.leaf (2575706351912648:ℤ))) (.branch 200 (.leaf (2830877581748166:ℤ)) (.leaf (3258744323435751:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 16 10) 8000 (endpointMeanRuns 16 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 16 10, EndpointRunConditions (endpointMeanCutoff 16 10) (endpointMeanBox 16 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 16 10 h) (endpointMeanCornerA 16 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 10, endpointJoint24Q (endpointMeanCornerK 16 10 h) (endpointMeanCornerA 16 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 16 10, endpointRunWeightQ (endpointMeanCutoff 16 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 16 10) = (223247697/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 16 10 h = (logRoundedQ ((endpointMeanCutoff 16 10:ℚ)/200)).2+(223247697/500000000000000:ℚ)+((endpointMeanRuns 16 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 16 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 16 10) r*endpointJoint24Q (endpointMeanCornerK 16 10 h) (endpointMeanCornerA 16 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 16 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 16 10 h≤endpointMeanCorner 16 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 16 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint16_10

namespace EndpointAnalyticJoint16_11
private noncomputable def weights : IntegerLookupTree := (.branch 1414 (.branch 1154 (.branch 1004 (.leaf (106522449600000:ℤ)) (.leaf (8923921600000:ℤ))) (.branch 1255 (.leaf (4338470300000:ℤ)) (.leaf (5458480400000:ℤ)))) (.branch 1825 (.branch 1521 (.leaf (2593616400000:ℤ)) (.leaf (5508090800000:ℤ))) (.branch 2181 (.leaf (3080947200000:ℤ)) (.branch 3345 (.leaf (3311281800000:ℤ)) (.leaf (465670200000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.branch 130 (.leaf (1832896513892746:ℤ)) (.leaf (2041657055177402:ℤ))) (.branch 155 (.leaf (2254061526747870:ℤ)) (.leaf (2386411577499061:ℤ)))) (.branch 180 (.branch 171 (.leaf (2562489828721738:ℤ)) (.leaf (2648233479696759:ℤ))) (.branch 187 (.leaf (2812452664974528:ℤ)) (.branch 200 (.leaf (2949707093610933:ℤ)) (.leaf (3229440814167809:ℤ)))))), (.branch 166 (.branch 146 (.branch 130 (.leaf (1840560253630305:ℤ)) (.leaf (2053525934457720:ℤ))) (.branch 155 (.leaf (2271078794518850:ℤ)) (.leaf (2407064972604084:ℤ)))) (.branch 180 (.branch 171 (.leaf (2588473731839948:ℤ)) (.leaf (2677011989439738:ℤ))) (.branch 187 (.leaf (2846937717285872:ℤ)) (.branch 200 (.leaf (2989310542017197:ℤ)) (.leaf (3280426532101846:ℤ)))))), (.branch 166 (.branch 146 (.branch 130 (.leaf (1836158625759979:ℤ)) (.leaf (2047008550991292:ℤ))) (.branch 155 (.leaf (2262148801219016:ℤ)) (.leaf (2396528323181018:ℤ)))) (.branch 180 (.branch 171 (.leaf (2575706351912648:ℤ)) (.leaf (2663128409617114:ℤ))) (.branch 187 (.leaf (2830877581748166:ℤ)) (.branch 200 (.leaf (2971405813990627:ℤ)) (.leaf (3258744323435751:ℤ)))))), (.branch 166 (.branch 146 (.branch 130 (.leaf (1844134089623417:ℤ)) (.leaf (2059398567283519:ℤ))) (.branch 155 (.leaf (2279969330085978:ℤ)) (.leaf (2418199080636658:ℤ)))) (.branch 180 (.branch 171 (.leaf (2603041366476405:ℤ)) (.leaf (2693441775096234:ℤ))) (.branch 187 (.leaf (2867290129481627:ℤ)) (.branch 200 (.leaf (3013307693629542:ℤ)) (.leaf (3312912048646309:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 16 11) 8000 (endpointMeanRuns 16 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 16 11, EndpointRunConditions (endpointMeanCutoff 16 11) (endpointMeanBox 16 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 16 11 h) (endpointMeanCornerA 16 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 11, endpointJoint24Q (endpointMeanCornerK 16 11 h) (endpointMeanCornerA 16 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 16 11, endpointRunWeightQ (endpointMeanCutoff 16 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 16 11) = (445047367/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 16 11 h = (logRoundedQ ((endpointMeanCutoff 16 11:ℚ)/200)).2+(445047367/1000000000000000:ℚ)+((endpointMeanRuns 16 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 16 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 16 11) r*endpointJoint24Q (endpointMeanCornerK 16 11 h) (endpointMeanCornerA 16 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 16 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 16 11 h≤endpointMeanCorner 16 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 16 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint16_11

namespace EndpointAnalyticJoint16_12
private noncomputable def weights : IntegerLookupTree := (.branch 1521 (.branch 1154 (.branch 1004 (.leaf (102811800100000:ℤ)) (.branch 1068 (.leaf (3723381500000:ℤ)) (.leaf (4400891000000:ℤ)))) (.branch 1255 (.leaf (4310338200000:ℤ)) (.branch 1414 (.leaf (5424820200000:ℤ)) (.leaf (2578375200000:ℤ))))) (.branch 2181 (.branch 1673 (.leaf (2845605000000:ℤ)) (.branch 1825 (.leaf (2006547300000:ℤ)) (.leaf (3065052800000:ℤ)))) (.branch 2641 (.leaf (1607903500000:ℤ)) (.branch 3345 (.leaf (720069100000:ℤ)) (.leaf (463766300000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.branch 130 (.leaf (1840560253630305:ℤ)) (.branch 138 (.leaf (2053525934457720:ℤ)) (.leaf (2158666100992367:ℤ)))) (.branch 155 (.leaf (2271078794518850:ℤ)) (.branch 160 (.leaf (2407064972604084:ℤ)) (.leaf (2487339095620040:ℤ))))) (.branch 187 (.branch 171 (.leaf (2588473731839948:ℤ)) (.branch 180 (.leaf (2677011989439738:ℤ)) (.leaf (2846937717285872:ℤ)))) (.branch 194 (.leaf (2989310542017197:ℤ)) (.branch 200 (.leaf (3141494377983619:ℤ)) (.leaf (3280426532101846:ℤ)))))), (.branch 166 (.branch 146 (.branch 130 (.leaf (1848256037133740:ℤ)) (.branch 138 (.leaf (2065463811758547:ℤ)) (.leaf (2173013018300653:ℤ)))) (.branch 155 (.leaf (2288224535891346:ℤ)) (.branch 160 (.leaf (2427897114214267:ℤ)) (.leaf (2510498388727263:ℤ))))) (.branch 187 (.branch 171 (.leaf (2614721114334233:ℤ)) (.branch 180 (.leaf (2706103236948992:ℤ)) (.leaf (2881845610076532:ℤ)))) (.branch 194 (.leaf (3029445715464594:ℤ)) (.branch 200 (.leaf (3187563462855129:ℤ)) (.leaf (3332217201599585:ℤ)))))), (.branch 166 (.branch 146 (.branch 130 (.leaf (1844134089623417:ℤ)) (.branch 138 (.leaf (2059398567283519:ℤ)) (.leaf (2165910778326561:ℤ)))) (.branch 155 (.leaf (2279969330085978:ℤ)) (.branch 160 (.leaf (2418199080636658:ℤ)) (.leaf (2499929774855655:ℤ))))) (.branch 187 (.branch 171 (.leaf (2603041366476405:ℤ)) (.branch 180 (.leaf (2693441775096234:ℤ)) (.leaf (2867290129481627:ℤ)))) (.branch 194 (.leaf (3013307693629542:ℤ)) (.branch 200 (.leaf (3169753915460526:ℤ)) (.leaf (3312912048646309:ℤ)))))), (.branch 166 (.branch 146 (.branch 130 (.leaf (1852144195387041:ℤ)) (.branch 138 (.leaf (2071863577157794:ℤ)) (.leaf (2180914684411573:ℤ)))) (.branch 155 (.leaf (2297930243727329:ℤ)) (.branch 160 (.leaf (2440065797273817:ℤ)) (.leaf (2524268189738877:ℤ))))) (.branch 187 (.branch 171 (.leaf (2630666477393982:ℤ)) (.branch 180 (.leaf (2724100185945054:ℤ)) (.leaf (2904171038560340:ℤ)))) (.branch 194 (.leaf (3055800461093010:ℤ)) (.branch 200 (.leaf (3218638525547585:ℤ)) (.leaf (3367980164364152:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 16 12) 8000 (endpointMeanRuns 16 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 16 12, EndpointRunConditions (endpointMeanCutoff 16 12) (endpointMeanBox 16 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 16 12 h) (endpointMeanCornerA 16 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 12, endpointJoint24Q (endpointMeanCornerK 16 12 h) (endpointMeanCornerA 16 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 16 12, endpointRunWeightQ (endpointMeanCutoff 16 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 16 12) = (443617329/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 16 12 h = (logRoundedQ ((endpointMeanCutoff 16 12:ℚ)/200)).2+(443617329/1000000000000000:ℚ)+((endpointMeanRuns 16 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 16 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 16 12) r*endpointJoint24Q (endpointMeanCornerK 16 12 h) (endpointMeanCornerA 16 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 16 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 16 12 h≤endpointMeanCorner 16 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 16 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint16_12

namespace EndpointAnalyticJoint16_13
private noncomputable def weights : IntegerLookupTree := (.branch 1414 (.branch 1154 (.branch 1035 (.branch 1004 (.leaf (99225559400000:ℤ)) (.leaf (1776891300000:ℤ))) (.branch 1068 (.leaf (1779602500000:ℤ)) (.branch 1103 (.leaf (1767721400000:ℤ)) (.leaf (2401263000000:ℤ))))) (.branch 1255 (.branch 1195 (.leaf (1736139500000:ℤ)) (.leaf (2330431900000:ℤ))) (.branch 1321 (.leaf (2254422100000:ℤ)) (.branch 1375 (.leaf (1601978400000:ℤ)) (.leaf (1030717000000:ℤ)))))) (.branch 2007 (.branch 1619 (.branch 1521 (.leaf (2563321000000:ℤ)) (.leaf (1850515700000:ℤ))) (.branch 1673 (.leaf (828392400000:ℤ)) (.branch 1825 (.leaf (1995727300000:ℤ)) (.leaf (1660844500000:ℤ))))) (.branch 2641 (.branch 2181 (.leaf (1039883500000:ℤ)) (.branch 2389 (.leaf (810045800000:ℤ)) (.leaf (583562400000:ℤ)))) (.branch 3345 (.leaf (716883200000:ℤ)) (.branch 4561 (.leaf (178428600000:ℤ)) (.leaf (16821200000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.branch 130 (.branch 122 (.leaf (1848256037133740:ℤ)) (.leaf (1964931385082545:ℤ))) (.branch 138 (.leaf (2065463811758547:ℤ)) (.branch 142 (.leaf (2173013018300653:ℤ)) (.leaf (2229617819787291:ℤ))))) (.branch 155 (.branch 150 (.leaf (2288224535891346:ℤ)) (.leaf (2348925692298710:ℤ))) (.branch 160 (.leaf (2427897114214267:ℤ)) (.branch 162 (.leaf (2510498388727263:ℤ)) (.leaf (2544603813559683:ℤ)))))) (.branch 184 (.branch 173 (.branch 171 (.leaf (2614721114334233:ℤ)) (.leaf (2706103236948992:ℤ))) (.branch 176 (.leaf (2743870790317346:ℤ)) (.branch 180 (.leaf (2801877542950271:ℤ)) (.leaf (2881845610076532:ℤ))))) (.branch 194 (.branch 187 (.leaf (2964954941849198:ℤ)) (.branch 191 (.leaf (3029445715464594:ℤ)) (.leaf (3118449431629115:ℤ)))) (.branch 197 (.leaf (3187563462855129:ℤ)) (.branch 200 (.leaf (3258791040829719:ℤ)) (.leaf (3332217201599585:ℤ))))))), (.branch 166 (.branch 146 (.branch 130 (.branch 122 (.leaf (1855983998385017:ℤ)) (.leaf (1974850116543036:ℤ))) (.branch 138 (.leaf (2077471088189938:ℤ)) (.branch 142 (.leaf (2187455288028724:ℤ)) (.leaf (2245423287643090:ℤ))))) (.branch 155 (.branch 150 (.leaf (2305499720789942:ℤ)) (.leaf (2367784827531418:ℤ))) (.branch 160 (.leaf (2448909549305941:ℤ)) (.branch 162 (.leaf (2533873315021848:ℤ)) (.leaf (2568986597782521:ℤ)))))) (.branch 184 (.branch 173 (.branch 171 (.leaf (2641234647911807:ℤ)) (.leaf (2735510620764321:ℤ))) (.branch 176 (.leaf (2774512278108459:ℤ)) (.branch 180 (.leaf (2834457307748399:ℤ)) (.leaf (2917181528029697:ℤ))))) (.branch 194 (.branch 187 (.leaf (3003256985136316:ℤ)) (.branch 191 (.leaf (3070119753016268:ℤ)) (.leaf (3162496476183559:ℤ)))) (.branch 197 (.leaf (3234308137215440:ℤ)) (.branch 200 (.leaf (3308386503871072:ℤ)) (.leaf (3384825531063426:ℤ))))))), (.branch 166 (.branch 146 (.branch 130 (.branch 122 (.leaf (1852144195387041:ℤ)) (.leaf (1970083197447320:ℤ))) (.branch 138 (.leaf (2071863577157794:ℤ)) (.branch 142 (.leaf (2180914684411573:ℤ)) (.leaf (2238380377579676:ℤ))))) (.branch 155 (.branch 150 (.leaf (2297930243727329:ℤ)) (.leaf (2359664330660193:ℤ))) (.branch 160 (.leaf (2440065797273817:ℤ)) (.branch 162 (.leaf (2524268189738877:ℤ)) (.leaf (2559066373595566:ℤ)))))) (.branch 184 (.branch 173 (.branch 171 (.leaf (2630666477393982:ℤ)) (.leaf (2724100185945054:ℤ))) (.branch 176 (.leaf (2762755265612926:ℤ)) (.branch 180 (.leaf (2822170551938645:ℤ)) (.leaf (2904171038560340:ℤ))))) (.branch 194 (.branch 187 (.leaf (2989504614765761:ℤ)) (.branch 191 (.leaf (3055800461093010:ℤ)) (.leaf (3147409548329857:ℤ)))) (.branch 197 (.leaf (3218638525547585:ℤ)) (.branch 200 (.leaf (3292130098951901:ℤ)) (.leaf (3367980164364152:ℤ))))))), (.branch 166 (.branch 146 (.branch 130 (.branch 122 (.leaf (1860189093519995:ℤ)) (.leaf (1980426790170463:ℤ))) (.branch 138 (.leaf (2084404034530986:ℤ)) (.branch 142 (.leaf (2196022527002220:ℤ)) (.leaf (2254928217947662:ℤ))))) (.branch 155 (.branch 150 (.leaf (2316032648052169:ℤ)) (.leaf (2379444412889484:ℤ))) (.branch 160 (.leaf (2462130245065671:ℤ)) (.branch 162 (.leaf (2548843554653651:ℤ)) (.leaf (2584714336446669:ℤ)))))) (.branch 184 (.branch 173 (.branch 171 (.leaf (2658584763350202:ℤ)) (.leaf (2755107569682198:ℤ))) (.branch 176 (.leaf (2795081947148761:ℤ)) (.branch 180 (.leaf (2856571577044257:ℤ)) (.leaf (2941526333345785:ℤ))))) (.branch 194 (.branch 187 (.leaf (3030045135254160:ℤ)) (.branch 191 (.leaf (3098892448905103:ℤ)) (.leaf (3194136076460863:ℤ)))) (.branch 197 (.leaf (3268277044350299:ℤ)) (.branch 200 (.leaf (3344850818425279:ℤ)) (.leaf (3423963637122621:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 16 13) 8000 (endpointMeanRuns 16 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 16 13, EndpointRunConditions (endpointMeanCutoff 16 13) (endpointMeanBox 16 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 16 13 h) (endpointMeanCornerA 16 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 13, endpointJoint24Q (endpointMeanCornerK 16 13 h) (endpointMeanCornerA 16 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 16 13, endpointRunWeightQ (endpointMeanCutoff 16 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 16 13) = (221102419/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 16 13 h = (logRoundedQ ((endpointMeanCutoff 16 13:ℚ)/200)).2+(221102419/500000000000000:ℚ)+((endpointMeanRuns 16 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 16 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 16 13) r*endpointJoint24Q (endpointMeanCornerK 16 13 h) (endpointMeanCornerA 16 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 16 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 16 13 h≤endpointMeanCorner 16 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 16 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint16_13

namespace EndpointAnalyticJoint16_14
private noncomputable def weights : IntegerLookupTree := (.branch 1521 (.branch 1224 (.branch 1103 (.branch 1035 (.branch 1004 (.leaf (95759334500000:ℤ)) (.leaf (1764422200000:ℤ))) (.branch 1068 (.leaf (1767333700000:ℤ)) (.leaf (1755751100000:ℤ)))) (.branch 1154 (.branch 1128 (.leaf (1166151800000:ℤ)) (.leaf (1152478900000:ℤ))) (.branch 1195 (.leaf (1724878300000:ℤ)) (.leaf (1120118800000:ℤ))))) (.branch 1375 (.branch 1287 (.branch 1255 (.leaf (1125840000000:ℤ)) (.leaf (1088838500000:ℤ))) (.branch 1321 (.leaf (1080330900000:ℤ)) (.leaf (1592300100000:ℤ)))) (.branch 1434 (.branch 1414 (.leaf (1024594900000:ℤ)) (.leaf (484579300000:ℤ))) (.branch 1476 (.leaf (970122000000:ℤ)) (.leaf (946578900000:ℤ)))))) (.branch 2091 (.branch 1761 (.branch 1619 (.branch 1568 (.leaf (895154900000:ℤ)) (.leaf (873194000000:ℤ))) (.branch 1673 (.leaf (823841500000:ℤ)) (.leaf (1174617600000:ℤ)))) (.branch 1930 (.branch 1825 (.leaf (705345900000:ℤ)) (.leaf (983011000000:ℤ))) (.branch 2007 (.leaf (572761700000:ℤ)) (.leaf (520745200000:ℤ))))) (.branch 2641 (.branch 2281 (.branch 2181 (.leaf (457890700000:ℤ)) (.leaf (409585300000:ℤ))) (.branch 2389 (.leaf (348333800000:ℤ)) (.leaf (580866200000:ℤ)))) (.branch 3345 (.branch 2951 (.leaf (377611300000:ℤ)) (.leaf (215612000000:ℤ))) (.branch 3859 (.leaf (100301300000:ℤ)) (.branch 4561 (.leaf (34869700000:ℤ)) (.leaf (16759400000:ℤ))))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 146 (.branch 134 (.branch 126 (.branch 122 (.leaf (1855983998385017:ℤ)) (.leaf (1974850116543036:ℤ))) (.branch 130 (.leaf (2025280799222529:ℤ)) (.leaf (2077471088189938:ℤ)))) (.branch 142 (.branch 138 (.leaf (2131501046709361:ℤ)) (.leaf (2187455288028724:ℤ))) (.branch 144 (.leaf (2245423287643090:ℤ)) (.leaf (2275191819924615:ℤ))))) (.branch 155 (.branch 150 (.branch 148 (.leaf (2305499720789942:ℤ)) (.leaf (2336359696991905:ℤ))) (.branch 152 (.leaf (2367784827531418:ℤ)) (.leaf (2399788576760847:ℤ)))) (.branch 160 (.branch 157 (.leaf (2448909549305941:ℤ)) (.leaf (2482421405319844:ℤ))) (.branch 162 (.leaf (2533873315021848:ℤ)) (.leaf (2568986597782521:ℤ)))))) (.branch 180 (.branch 171 (.branch 168 (.branch 166 (.leaf (2604768182918129:ℤ)) (.leaf (2641234647911807:ℤ))) (.branch 170 (.leaf (2678403082202915:ℤ)) (.leaf (2716291106198739:ℤ)))) (.branch 176 (.branch 173 (.leaf (2735510620764321:ℤ)) (.leaf (2774512278108459:ℤ))) (.branch 178 (.leaf (2834457307748399:ℤ)) (.leaf (2875411226908102:ℤ))))) (.branch 189 (.branch 184 (.branch 182 (.leaf (2917181528029697:ℤ)) (.leaf (2959789465932028:ℤ))) (.branch 187 (.leaf (3003256985136316:ℤ)) (.leaf (3070119753016268:ℤ)))) (.branch 194 (.branch 191 (.leaf (3115837005281672:ℤ)) (.leaf (3162496476183559:ℤ))) (.branch 197 (.leaf (3234308137215440:ℤ)) (.branch 200 (.leaf (3308386503871072:ℤ)) (.leaf (3384825531063426:ℤ)))))))), (.branch 164 (.branch 146 (.branch 134 (.branch 126 (.branch 122 (.leaf (1863744271926317:ℤ)) (.leaf (1984818916537486:ℤ))) (.branch 130 (.leaf (2036262657564473:ℤ)) (.leaf (2089548167193750:ℤ)))) (.branch 142 (.branch 138 (.leaf (2144761457247924:ℤ)) (.leaf (2201993543907434:ℤ))) (.branch 144 (.leaf (2261340798384412:ℤ)) (.leaf (2291839286591678:ℤ))))) (.branch 155 (.branch 150 (.branch 148 (.leaf (2322905326461763:ℤ)) (.leaf (2354552644688197:ℤ))) (.branch 152 (.leaf (2386795379636489:ℤ)) (.leaf (2419648096137298:ℤ)))) (.branch 160 (.branch 157 (.leaf (2470103838243840:ℤ)) (.leaf (2504548169296252:ℤ))) (.branch 162 (.leaf (2557465882236551:ℤ)) (.leaf (2593603021585436:ℤ)))))) (.branch 180 (.branch 171 (.branch 168 (.branch 166 (.leaf (2630447397815832:ℤ)) (.leaf (2668017031371276:ℤ))) (.branch 170 (.leaf (2706330512592309:ℤ)) (.leaf (2745407023324926:ℤ)))) (.branch 176 (.branch 173 (.leaf (2765237576357644:ℤ)) (.leaf (2805495947017344:ℤ))) (.branch 178 (.leaf (2867415904618249:ℤ)) (.leaf (2909748993277797:ℤ))))) (.branch 189 (.branch 184 (.branch 182 (.leaf (2952950719400847:ℤ)) (.leaf (2997044324844050:ℤ))) (.branch 187 (.leaf (3042053823976396:ℤ)) (.leaf (3111339889586092:ℤ)))) (.branch 194 (.branch 191 (.leaf (3158749537271662:ℤ)) (.leaf (3207165670359634:ℤ))) (.branch 197 (.leaf (3281738308384370:ℤ)) (.branch 200 (.leaf (3358736759080284:ℤ)) (.leaf (3438264429533284:ℤ)))))))), (.branch 164 (.branch 146 (.branch 134 (.branch 126 (.branch 122 (.leaf (1860189093519995:ℤ)) (.leaf (1980426790170463:ℤ))) (.branch 130 (.leaf (2031503829616489:ℤ)) (.leaf (2084404034530986:ℤ)))) (.branch 142 (.branch 138 (.leaf (2139213277221910:ℤ)) (.leaf (2196022527002220:ℤ))) (.branch 144 (.leaf (2254928217947662:ℤ)) (.leaf (2285198956313736:ℤ))))) (.branch 155 (.branch 150 (.branch 148 (.leaf (2316032648052169:ℤ)) (.leaf (2347443067786497:ℤ))) (.branch 152 (.leaf (2379444412889484:ℤ)) (.leaf (2412051319169258:ℤ)))) (.branch 160 (.branch 157 (.leaf (2462130245065671:ℤ)) (.leaf (2496318112856195:ℤ))) (.branch 162 (.leaf (2548843554653651:ℤ)) (.leaf (2584714336446669:ℤ)))))) (.branch 180 (.branch 171 (.branch 168 (.branch 166 (.leaf (2621288670617390:ℤ)) (.leaf (2658584763350202:ℤ))) (.branch 170 (.leaf (2696621412562688:ℤ)) (.leaf (2735418031176946:ℤ)))) (.branch 176 (.branch 173 (.leaf (2755107569682198:ℤ)) (.leaf (2795081947148761:ℤ))) (.branch 178 (.leaf (2856571577044257:ℤ)) (.leaf (2898615379040549:ℤ))))) (.branch 189 (.branch 184 (.branch 182 (.leaf (2941526333345785:ℤ)) (.leaf (2985328096165711:ℤ))) (.branch 187 (.leaf (3030045135254160:ℤ)) (.leaf (3098892448905103:ℤ)))) (.branch 194 (.branch 191 (.leaf (3146010359570284:ℤ)) (.leaf (3194136076460863:ℤ))) (.branch 197 (.leaf (3268277044350299:ℤ)) (.branch 200 (.leaf (3344850818425279:ℤ)) (.leaf (3423963637122621:ℤ)))))))), (.branch 164 (.branch 146 (.branch 134 (.branch 126 (.branch 122 (.leaf (1868268935145002:ℤ)) (.leaf (1990824690199289:ℤ))) (.branch 130 (.leaf (2042967079031380:ℤ)) (.leaf (2097020396067396:ℤ)))) (.branch 142 (.branch 138 (.leaf (2153077040683481:ℤ)) (.leaf (2211235026097485:ℤ))) (.branch 144 (.leaf (2271598392760492:ℤ)) (.leaf (2302641364554991:ℤ))))) (.branch 155 (.branch 150 (.branch 148 (.leaf (2334277657681596:ℤ)) (.leaf (2366522178922096:ℤ))) (.branch 152 (.leaf (2399390303300863:ℤ)) (.leaf (2432897891812836:ℤ)))) (.branch 160 (.branch 157 (.leaf (2484394212008567:ℤ)) (.leaf (2519573211213370:ℤ))) (.branch 162 (.leaf (2573658176460049:ℤ)) (.leaf (2610619353200399:ℤ)))))) (.branch 180 (.branch 171 (.branch 168 (.branch 166 (.leaf (2648326462709837:ℤ)) (.leaf (2686799335702825:ℤ))) (.branch 170 (.leaf (2726058462739149:ℤ)) (.leaf (2766125020706335:ℤ)))) (.branch 176 (.branch 173 (.leaf (2786467898531708:ℤ)) (.leaf (2827786879466387:ℤ))) (.branch 178 (.leaf (2891391935604934:ℤ)) (.leaf (2934914711427295:ℤ))))) (.branch 189 (.branch 184 (.branch 182 (.leaf (2979362115688595:ℤ)) (.leaf (3024760074241322:ℤ))) (.branch 187 (.leaf (3071135423685165:ℤ)) (.leaf (3142592107092682:ℤ)))) (.branch 194 (.branch 191 (.leaf (3191534674348147:ℤ)) (.leaf (3241556307904903:ℤ))) (.branch 197 (.leaf (3318681098807110:ℤ)) (.branch 200 (.leaf (3398415816277163:ℤ)) (.leaf (3480877682232817:ℤ))))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 16 14) 8000 (endpointMeanRuns 16 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 16 14, EndpointRunConditions (endpointMeanCutoff 16 14) (endpointMeanBox 16 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 16 14 h) (endpointMeanCornerA 16 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 14, endpointJoint24Q (endpointMeanCornerK 16 14 h) (endpointMeanCornerA 16 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 16 14, endpointRunWeightQ (endpointMeanCutoff 16 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 16 14) = (110202367/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 16 14 h = (logRoundedQ ((endpointMeanCutoff 16 14:ℚ)/200)).2+(110202367/250000000000000:ℚ)+((endpointMeanRuns 16 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 16 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 16 14) r*endpointJoint24Q (endpointMeanCornerK 16 14 h) (endpointMeanCornerA 16 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 16 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 16 14 h≤endpointMeanCorner 16 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 16 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint16_14

namespace EndpointAnalyticJoint16_15
private noncomputable def weights : IntegerLookupTree := (.branch 1476 (.branch 1195 (.branch 1091 (.branch 1035 (.branch 1004 (.leaf (92959441900000:ℤ)) (.leaf (1754145600000:ℤ))) (.branch 1068 (.leaf (1757222200000:ℤ)) (.leaf (1145099900000:ℤ)))) (.branch 1128 (.branch 1103 (.leaf (569613600000:ℤ)) (.leaf (1159699200000:ℤ))) (.branch 1154 (.leaf (1146180800000:ℤ)) (.branch 1181 (.leaf (1128845100000:ℤ)) (.leaf (553433700000:ℤ)))))) (.branch 1321 (.branch 1255 (.branch 1224 (.leaf (1114186700000:ℤ)) (.leaf (1119954000000:ℤ))) (.branch 1287 (.leaf (1083219700000:ℤ)) (.leaf (1074828800000:ℤ)))) (.branch 1375 (.branch 1356 (.leaf (1029993000000:ℤ)) (.leaf (519355600000:ℤ))) (.branch 1414 (.leaf (1019549100000:ℤ)) (.branch 1434 (.leaf (482217800000:ℤ)) (.leaf (965442400000:ℤ))))))) (.branch 2091 (.branch 1673 (.branch 1568 (.branch 1521 (.leaf (942076900000:ℤ)) (.leaf (890957900000:ℤ))) (.branch 1619 (.leaf (869159000000:ℤ)) (.leaf (820090700000:ℤ)))) (.branch 1825 (.branch 1761 (.leaf (1169368600000:ℤ)) (.leaf (702255000000:ℤ))) (.branch 1930 (.leaf (978786400000:ℤ)) (.branch 2007 (.leaf (570350300000:ℤ)) (.leaf (518589200000:ℤ)))))) (.branch 2641 (.branch 2281 (.branch 2181 (.leaf (456027000000:ℤ)) (.leaf (407947100000:ℤ))) (.branch 2389 (.leaf (346965500000:ℤ)) (.branch 2509 (.leaf (296505200000:ℤ)) (.leaf (243602600000:ℤ))))) (.branch 3345 (.branch 2951 (.leaf (376221900000:ℤ)) (.leaf (214850800000:ℤ))) (.branch 3859 (.leaf (99962700000:ℤ)) (.branch 4561 (.leaf (34757500000:ℤ)) (.leaf (16708500000:ℤ))))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.branch 134 (.branch 126 (.branch 122 (.leaf (1863744271926317:ℤ)) (.leaf (1984818916537486:ℤ))) (.branch 130 (.leaf (2036262657564473:ℤ)) (.leaf (2089548167193750:ℤ)))) (.branch 140 (.branch 138 (.leaf (2144761457247924:ℤ)) (.leaf (2201993543907434:ℤ))) (.branch 142 (.leaf (2231396532618004:ℤ)) (.branch 144 (.leaf (2261340798384412:ℤ)) (.leaf (2291839286591678:ℤ)))))) (.branch 155 (.branch 150 (.branch 148 (.leaf (2322905326461763:ℤ)) (.leaf (2354552644688197:ℤ))) (.branch 152 (.leaf (2386795379636489:ℤ)) (.leaf (2419648096137298:ℤ)))) (.branch 160 (.branch 157 (.leaf (2470103838243840:ℤ)) (.leaf (2504548169296252:ℤ))) (.branch 162 (.leaf (2557465882236551:ℤ)) (.branch 164 (.leaf (2593603021585436:ℤ)) (.leaf (2630447397815832:ℤ))))))) (.branch 182 (.branch 173 (.branch 170 (.branch 168 (.leaf (2668017031371276:ℤ)) (.leaf (2706330512592309:ℤ))) (.branch 171 (.leaf (2745407023324926:ℤ)) (.leaf (2765237576357644:ℤ)))) (.branch 176 (.branch 174 (.leaf (2805495947017344:ℤ)) (.leaf (2825928954638984:ℤ))) (.branch 178 (.leaf (2867415904618249:ℤ)) (.branch 180 (.leaf (2909748993277797:ℤ)) (.leaf (2952950719400847:ℤ)))))) (.branch 191 (.branch 185 (.branch 184 (.leaf (2997044324844050:ℤ)) (.leaf (3042053823976396:ℤ))) (.branch 187 (.leaf (3064909756951430:ℤ)) (.branch 189 (.leaf (3111339889586092:ℤ)) (.leaf (3158749537271662:ℤ))))) (.branch 194 (.branch 192 (.leaf (3207165670359634:ℤ)) (.leaf (3231759848510016:ℤ))) (.branch 197 (.leaf (3281738308384370:ℤ)) (.branch 200 (.leaf (3358736759080284:ℤ)) (.leaf (3438264429533284:ℤ)))))))), (.branch 166 (.branch 146 (.branch 134 (.branch 126 (.branch 122 (.leaf (1871536992862357:ℤ)) (.leaf (1994838037805688:ℤ))) (.branch 130 (.leaf (2047304063803526:ℤ)) (.leaf (2101695454557186:ℤ)))) (.branch 140 (.branch 138 (.leaf (2158104362931365:ℤ)) (.leaf (2216628423879513:ℤ))) (.branch 142 (.leaf (2246715742266257:ℤ)) (.branch 144 (.leaf (2277371146268554:ℤ)) (.leaf (2308608561953729:ℤ)))))) (.branch 155 (.branch 150 (.branch 148 (.leaf (2340442337531766:ℤ)) (.leaf (2372887258646882:ℤ))) (.branch 152 (.leaf (2405958564314894:ℤ)) (.leaf (2439671963537441:ℤ)))) (.branch 160 (.branch 157 (.leaf (2491481554897035:ℤ)) (.leaf (2526872157516303:ℤ))) (.branch 162 (.leaf (2581278116797871:ℤ)) (.branch 164 (.leaf (2618455323738739:ℤ)) (.leaf (2656379772316022:ℤ))))))) (.branch 182 (.branch 173 (.branch 170 (.branch 168 (.leaf (2695070990877317:ℤ)) (.leaf (2734549139393980:ℤ))) (.branch 171 (.leaf (2774835033889174:ℤ)) (.leaf (2795287576534354:ℤ)))) (.branch 176 (.branch 174 (.leaf (2836825618265679:ℤ)) (.leaf (2857916759505409:ℤ))) (.branch 178 (.leaf (2900757738555972:ℤ)) (.branch 180 (.leaf (2944496816542380:ℤ)) (.leaf (2989158496797267:ℤ)))))) (.branch 191 (.branch 185 (.branch 184 (.leaf (3034768110525538:ℤ)) (.leaf (3081351850264450:ℤ))) (.branch 187 (.leaf (3105017446665240:ℤ)) (.branch 189 (.leaf (3153113457225560:ℤ)) (.leaf (3202253077519999:ℤ))))) (.branch 194 (.branch 192 (.leaf (3252465801810546:ℤ)) (.leaf (3277984076122962:ℤ))) (.branch 197 (.leaf (3329864028969648:ℤ)) (.branch 200 (.leaf (3409853293621327:ℤ)) (.leaf (3492547009854233:ℤ)))))))), (.branch 166 (.branch 146 (.branch 134 (.branch 126 (.branch 122 (.leaf (1868268935145002:ℤ)) (.leaf (1990824690199289:ℤ))) (.branch 130 (.leaf (2042967079031380:ℤ)) (.leaf (2097020396067396:ℤ)))) (.branch 140 (.branch 138 (.leaf (2153077040683481:ℤ)) (.leaf (2211235026097485:ℤ))) (.branch 142 (.leaf (2241134286780632:ℤ)) (.branch 144 (.leaf (2271598392760492:ℤ)) (.leaf (2302641364554991:ℤ)))))) (.branch 155 (.branch 150 (.branch 148 (.leaf (2334277657681596:ℤ)) (.leaf (2366522178922096:ℤ))) (.branch 152 (.leaf (2399390303300863:ℤ)) (.leaf (2432897891812836:ℤ)))) (.branch 160 (.branch 157 (.leaf (2484394212008567:ℤ)) (.leaf (2519573211213370:ℤ))) (.branch 162 (.leaf (2573658176460049:ℤ)) (.branch 164 (.leaf (2610619353200399:ℤ)) (.leaf (2648326462709837:ℤ))))))) (.branch 182 (.branch 173 (.branch 170 (.branch 168 (.leaf (2686799335702825:ℤ)) (.leaf (2726058462739149:ℤ))) (.branch 171 (.leaf (2766125020706335:ℤ)) (.leaf (2786467898531708:ℤ)))) (.branch 176 (.branch 174 (.leaf (2827786879466387:ℤ)) (.leaf (2848768736320313:ℤ))) (.branch 178 (.leaf (2891391935604934:ℤ)) (.branch 180 (.leaf (2934914711427295:ℤ)) (.leaf (2979362115688595:ℤ)))))) (.branch 191 (.branch 185 (.branch 184 (.leaf (3024760074241322:ℤ)) (.leaf (3071135423685165:ℤ))) (.branch 187 (.leaf (3094698264925305:ℤ)) (.branch 189 (.leaf (3142592107092682:ℤ)) (.leaf (3191534674348147:ℤ))))) (.branch 194 (.branch 192 (.leaf (3241556307904903:ℤ)) (.leaf (3266981555767572:ℤ))) (.branch 197 (.leaf (3318681098807110:ℤ)) (.branch 200 (.leaf (3398415816277163:ℤ)) (.leaf (3480877682232817:ℤ)))))))), (.branch 166 (.branch 146 (.branch 134 (.branch 126 (.branch 122 (.leaf (1876383872041191:ℤ)) (.leaf (2001277182665232:ℤ))) (.branch 130 (.leaf (2054495012590715:ℤ)) (.leaf (2109713121195399:ℤ)))) (.branch 140 (.branch 138 (.leaf (2167030652099612:ℤ)) (.leaf (2226552906684004:ℤ))) (.branch 142 (.leaf (2257175508753568:ℤ)) (.branch 144 (.leaf (2288391806409077:ℤ)) (.leaf (2320216906764472:ℤ)))))) (.branch 155 (.branch 150 (.branch 148 (.leaf (2352666396017378:ℤ)) (.leaf (2385756357708420:ℤ))) (.branch 152 (.leaf (2419503391795183:ℤ)) (.leaf (2453924634582777:ℤ)))) (.branch 160 (.branch 157 (.leaf (2506859502266920:ℤ)) (.leaf (2543044948466376:ℤ))) (.branch 162 (.leaf (2598714384476894:ℤ)) (.branch 164 (.leaf (2636784000151380:ℤ)) (.leaf (2675643141370335:ℤ))))))) (.branch 182 (.branch 173 (.branch 170 (.branch 168 (.leaf (2715313338829304:ℤ)) (.leaf (2755816855733348:ℤ))) (.branch 171 (.leaf (2797176717770448:ℤ)) (.leaf (2818185189931922:ℤ)))) (.branch 176 (.branch 174 (.leaf (2860874488434693:ℤ)) (.leaf (2882561582387080:ℤ))) (.branch 178 (.leaf (2926636739112141:ℤ)) (.branch 180 (.leaf (2971668620002820:ℤ)) (.leaf (3017684565925307:ℤ)))))) (.branch 191 (.branch 185 (.branch 184 (.leaf (3064712893190992:ℤ)) (.leaf (3112782935433969:ℤ))) (.branch 187 (.leaf (3137218055386044:ℤ)) (.branch 189 (.leaf (3186908004842363:ℤ)) (.leaf (3237717748315945:ℤ))))) (.branch 194 (.branch 192 (.leaf (3289680541400327:ℤ)) (.leaf (3316105059766928:ℤ))) (.branch 197 (.leaf (3369862495169514:ℤ)) (.branch 200 (.leaf (3452838612922076:ℤ)) (.leaf (3538737767918817:ℤ))))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 16 15) 8000 (endpointMeanRuns 16 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 16 15, EndpointRunConditions (endpointMeanCutoff 16 15) (endpointMeanBox 16 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 16 15 h) (endpointMeanCornerA 16 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 15, endpointJoint24Q (endpointMeanCornerK 16 15 h) (endpointMeanCornerA 16 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 16 15, endpointRunWeightQ (endpointMeanCutoff 16 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 16 15) = (219829721/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 16 15 h = (logRoundedQ ((endpointMeanCutoff 16 15:ℚ)/200)).2+(219829721/500000000000000:ℚ)+((endpointMeanRuns 16 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 16 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 16 15) r*endpointJoint24Q (endpointMeanCornerK 16 15 h) (endpointMeanCornerA 16 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 16 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 16 15 h≤endpointMeanCorner 16 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 16 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint16_15

namespace EndpointAnalyticJoint16_16
private noncomputable def weights : IntegerLookupTree := (.branch 1521 (.branch 1224 (.branch 1103 (.branch 1035 (.branch 1004 (.leaf (89702399800000:ℤ)) (.leaf (1741947500000:ℤ))) (.branch 1068 (.leaf (1745220100000:ℤ)) (.leaf (1734175400000:ℤ)))) (.branch 1154 (.branch 1128 (.leaf (1152040300000:ℤ)) (.leaf (1138705300000:ℤ))) (.branch 1195 (.leaf (1704580800000:ℤ)) (.leaf (1107145500000:ℤ))))) (.branch 1375 (.branch 1287 (.branch 1255 (.leaf (1112967500000:ℤ)) (.leaf (1076550400000:ℤ))) (.branch 1321 (.leaf (1068298100000:ℤ)) (.leaf (1574855600000:ℤ)))) (.branch 1434 (.branch 1414 (.leaf (1013560100000:ℤ)) (.leaf (479414700000:ℤ))) (.branch 1476 (.leaf (959888000000:ℤ)) (.leaf (936733200000:ℤ)))))) (.branch 2091 (.branch 1761 (.branch 1619 (.branch 1568 (.leaf (885976200000:ℤ)) (.leaf (864369600000:ℤ))) (.branch 1673 (.leaf (815638700000:ℤ)) (.leaf (1163138300000:ℤ)))) (.branch 1930 (.branch 1825 (.leaf (698586100000:ℤ)) (.leaf (973772100000:ℤ))) (.branch 2007 (.leaf (567488100000:ℤ)) (.leaf (516030100000:ℤ))))) (.branch 2641 (.branch 2281 (.branch 2181 (.leaf (453814800000:ℤ)) (.leaf (406002600000:ℤ))) (.branch 2389 (.leaf (345341300000:ℤ)) (.leaf (576006500000:ℤ)))) (.branch 3345 (.branch 2951 (.leaf (374572700000:ℤ)) (.leaf (213947300000:ℤ))) (.branch 3859 (.leaf (99560700000:ℤ)) (.branch 4561 (.leaf (34624400000:ℤ)) (.leaf (16648000000:ℤ))))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 146 (.branch 134 (.branch 126 (.branch 122 (.leaf (1871536992862357:ℤ)) (.leaf (1994838037805688:ℤ))) (.branch 130 (.leaf (2047304063803526:ℤ)) (.leaf (2101695454557186:ℤ)))) (.branch 142 (.branch 138 (.leaf (2158104362931365:ℤ)) (.leaf (2216628423879513:ℤ))) (.branch 144 (.leaf (2277371146268554:ℤ)) (.leaf (2308608561953729:ℤ))))) (.branch 155 (.branch 150 (.branch 148 (.leaf (2340442337531766:ℤ)) (.leaf (2372887258646882:ℤ))) (.branch 152 (.leaf (2405958564314894:ℤ)) (.leaf (2439671963537441:ℤ)))) (.branch 160 (.branch 157 (.leaf (2491481554897035:ℤ)) (.leaf (2526872157516303:ℤ))) (.branch 162 (.leaf (2581278116797871:ℤ)) (.leaf (2618455323738739:ℤ)))))) (.branch 180 (.branch 171 (.branch 168 (.branch 166 (.leaf (2656379772316022:ℤ)) (.leaf (2695070990877317:ℤ))) (.branch 170 (.leaf (2734549139393980:ℤ)) (.leaf (2774835033889174:ℤ)))) (.branch 176 (.branch 173 (.leaf (2795287576534354:ℤ)) (.leaf (2836825618265679:ℤ))) (.branch 178 (.leaf (2900757738555972:ℤ)) (.leaf (2944496816542380:ℤ))))) (.branch 189 (.branch 184 (.branch 182 (.leaf (2989158496797267:ℤ)) (.leaf (3034768110525538:ℤ))) (.branch 187 (.leaf (3081351850264450:ℤ)) (.leaf (3153113457225560:ℤ)))) (.branch 194 (.branch 191 (.leaf (3202253077519999:ℤ)) (.leaf (3252465801810546:ℤ))) (.branch 197 (.leaf (3329864028969648:ℤ)) (.branch 200 (.leaf (3409853293621327:ℤ)) (.leaf (3492547009854233:ℤ)))))))), (.branch 164 (.branch 146 (.branch 134 (.branch 126 (.branch 122 (.leaf (1879362296862773:ℤ)) (.leaf (2004907734363229:ℤ))) (.branch 130 (.leaf (2058405340831488:ℤ)) (.leaf (2113913358426431:ℤ)))) (.branch 142 (.branch 138 (.leaf (2171530276975233:ℤ)) (.leaf (2231360570127590:ℤ))) (.branch 144 (.leaf (2293515131183199:ℤ)) (.leaf (2325500537279000:ℤ))))) (.branch 155 (.branch 150 (.branch 148 (.leaf (2358111746058417:ℤ)) (.leaf (2391364642005848:ℤ))) (.branch 152 (.leaf (2425275607028284:ℤ)) (.leaf (2459861539028065:ℤ)))) (.branch 160 (.branch 157 (.leaf (2513044286755758:ℤ)) (.leaf (2549395127914514:ℤ))) (.branch 162 (.leaf (2605312064000110:ℤ)) (.leaf (2643545764464975:ℤ)))))) (.branch 180 (.branch 171 (.branch 168 (.branch 166 (.leaf (2682567802203112:ℤ)) (.leaf (2722399280238216:ℤ))) (.branch 170 (.leaf (2763061998882624:ℤ)) (.leaf (2804578483220209:ℤ)))) (.branch 176 (.branch 173 (.leaf (2825664131839036:ℤ)) (.leaf (2868505155747670:ℤ))) (.branch 178 (.leaf (2934487265778274:ℤ)) (.leaf (2979659593545046:ℤ))))) (.branch 189 (.branch 184 (.branch 182 (.leaf (3025810237967060:ℤ)) (.leaf (3072966725355983:ℤ))) (.branch 187 (.leaf (3121157538467607:ℤ)) (.leaf (3195447886427968:ℤ)))) (.branch 194 (.branch 191 (.leaf (3246355765624732:ℤ)) (.leaf (3298405782312106:ℤ))) (.branch 197 (.leaf (3378695498997500:ℤ)) (.branch 200 (.leaf (3461747769481060:ℤ)) (.leaf (3547686591894127:ℤ)))))))), (.branch 164 (.branch 146 (.branch 134 (.branch 126 (.branch 122 (.leaf (1876383872041191:ℤ)) (.leaf (2001277182665232:ℤ))) (.branch 130 (.leaf (2054495012590715:ℤ)) (.leaf (2109713121195399:ℤ)))) (.branch 142 (.branch 138 (.leaf (2167030652099612:ℤ)) (.leaf (2226552906684004:ℤ))) (.branch 144 (.leaf (2288391806409077:ℤ)) (.leaf (2320216906764472:ℤ))))) (.branch 155 (.branch 150 (.branch 148 (.leaf (2352666396017378:ℤ)) (.leaf (2385756357708420:ℤ))) (.branch 152 (.leaf (2419503391795183:ℤ)) (.leaf (2453924634582777:ℤ)))) (.branch 160 (.branch 157 (.leaf (2506859502266920:ℤ)) (.leaf (2543044948466376:ℤ))) (.branch 162 (.leaf (2598714384476894:ℤ)) (.leaf (2636784000151380:ℤ)))))) (.branch 180 (.branch 171 (.branch 168 (.branch 166 (.leaf (2675643141370335:ℤ)) (.leaf (2715313338829304:ℤ))) (.branch 170 (.leaf (2755816855733348:ℤ)) (.leaf (2797176717770448:ℤ)))) (.branch 176 (.branch 173 (.leaf (2818185189931922:ℤ)) (.leaf (2860874488434693:ℤ))) (.branch 178 (.leaf (2926636739112141:ℤ)) (.leaf (2971668620002820:ℤ))))) (.branch 189 (.branch 184 (.branch 182 (.leaf (3017684565925307:ℤ)) (.leaf (3064712893190992:ℤ))) (.branch 187 (.leaf (3112782935433969:ℤ)) (.leaf (3186908004842363:ℤ)))) (.branch 194 (.branch 191 (.leaf (3237717748315945:ℤ)) (.leaf (3289680541400327:ℤ))) (.branch 197 (.leaf (3369862495169514:ℤ)) (.branch 200 (.leaf (3452838612922076:ℤ)) (.leaf (3538737767918817:ℤ)))))))), (.branch 164 (.branch 146 (.branch 134 (.branch 126 (.branch 122 (.leaf (1884534056646949:ℤ)) (.leaf (2011784554196763:ℤ))) (.branch 130 (.leaf (2066087995290349:ℤ)) (.leaf (2122482672124185:ℤ)))) (.branch 142 (.branch 138 (.leaf (2181074693754822:ℤ)) (.leaf (2241976898770611:ℤ))) (.branch 144 (.leaf (2305309369970286:ℤ)) (.leaf (2337926599123740:ℤ))))) (.branch 155 (.branch 150 (.branch 148 (.leaf (2371199995311099:ℤ)) (.leaf (2405146864475476:ℤ))) (.branch 152 (.leaf (2439785079924262:ℤ)) (.leaf (2475133104630717:ℤ)))) (.branch 160 (.branch 157 (.leaf (2529527936319427:ℤ)) (.leaf (2566735342770989:ℤ))) (.branch 162 (.leaf (2624014530700421:ℤ)) (.leaf (2663210879414868:ℤ)))))) (.branch 180 (.branch 171 (.branch 168 (.branch 166 (.leaf (2703241583228671:ℤ)) (.leaf (2744129950477188:ℤ))) (.branch 170 (.leaf (2785900099410576:ℤ)) (.leaf (2828576991953582:ℤ)))) (.branch 176 (.branch 173 (.leaf (2850263507050145:ℤ)) (.leaf (2894349251709142:ℤ))) (.branch 178 (.leaf (2962311161364209:ℤ)) (.leaf (3008882797420332:ℤ))))) (.branch 189 (.branch 184 (.branch 182 (.leaf (3056499943887863:ℤ)) (.leaf (3105193432588842:ℤ))) (.branch 187 (.leaf (3154995226977722:ℤ)) (.leaf (3231848832180874:ℤ)))) (.branch 194 (.branch 191 (.leaf (3284569114042645:ℤ)) (.leaf (3338519228580808:ℤ))) (.branch 197 (.leaf (3421833221767519:ℤ)) (.branch 200 (.leaf (3508132945292671:ℤ)) (.leaf (3597559619521690:ℤ))))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 16 16) 8000 (endpointMeanRuns 16 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 16 16, EndpointRunConditions (endpointMeanCutoff 16 16) (endpointMeanBox 16 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 16 16 h) (endpointMeanCornerA 16 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 16, endpointJoint24Q (endpointMeanCornerK 16 16 h) (endpointMeanCornerA 16 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 16 16, endpointRunWeightQ (endpointMeanCutoff 16 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 16 16) = (438294407/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 16 16 h = (logRoundedQ ((endpointMeanCutoff 16 16:ℚ)/200)).2+(438294407/1000000000000000:ℚ)+((endpointMeanRuns 16 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 16 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 16 16) r*endpointJoint24Q (endpointMeanCornerK 16 16 h) (endpointMeanCornerA 16 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 16 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 16 16 h≤endpointMeanCorner 16 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 16 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint16_16

namespace EndpointAnalyticJoint16_17
private noncomputable def weights : IntegerLookupTree := (.branch 1414 (.branch 1154 (.branch 1035 (.branch 1004 (.leaf (86553831700000:ℤ)) (.leaf (1729892500000:ℤ))) (.branch 1068 (.leaf (1733358700000:ℤ)) (.branch 1103 (.leaf (1722602500000:ℤ)) (.leaf (2341259200000:ℤ))))) (.branch 1255 (.branch 1195 (.leaf (1693693500000:ℤ)) (.leaf (2274694100000:ℤ))) (.branch 1321 (.leaf (2201878500000:ℤ)) (.branch 1375 (.leaf (1565498700000:ℤ)) (.leaf (1007641200000:ℤ)))))) (.branch 2007 (.branch 1619 (.branch 1521 (.leaf (2507265900000:ℤ)) (.leaf (1811328500000:ℤ))) (.branch 1673 (.leaf (811238900000:ℤ)) (.branch 1825 (.leaf (1955438600000:ℤ)) (.leaf (1628599300000:ℤ))))) (.branch 2641 (.branch 2181 (.leaf (1020437700000:ℤ)) (.branch 2389 (.leaf (795413500000:ℤ)) (.leaf (573399800000:ℤ)))) (.branch 3345 (.leaf (705020700000:ℤ)) (.branch 4561 (.leaf (175710500000:ℤ)) (.leaf (16588300000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.branch 130 (.branch 122 (.leaf (1879362296862773:ℤ)) (.leaf (2004907734363229:ℤ))) (.branch 138 (.leaf (2113913358426431:ℤ)) (.branch 142 (.leaf (2231360570127590:ℤ)) (.leaf (2293515131183199:ℤ))))) (.branch 155 (.branch 150 (.leaf (2358111746058417:ℤ)) (.leaf (2425275607028284:ℤ))) (.branch 160 (.leaf (2513044286755758:ℤ)) (.branch 162 (.leaf (2605312064000110:ℤ)) (.leaf (2643545764464975:ℤ)))))) (.branch 184 (.branch 173 (.branch 171 (.leaf (2722399280238216:ℤ)) (.leaf (2825664131839036:ℤ))) (.branch 176 (.leaf (2868505155747670:ℤ)) (.branch 180 (.leaf (2934487265778274:ℤ)) (.leaf (3025810237967060:ℤ))))) (.branch 194 (.branch 187 (.leaf (3121157538467607:ℤ)) (.branch 191 (.leaf (3195447886427968:ℤ)) (.leaf (3298405782312106:ℤ)))) (.branch 197 (.leaf (3378695498997500:ℤ)) (.branch 200 (.leaf (3461747769481060:ℤ)) (.leaf (3547686591894127:ℤ))))))), (.branch 166 (.branch 146 (.branch 130 (.branch 122 (.leaf (1887220320164453:ℤ)) (.leaf (2015028261507932:ℤ))) (.branch 138 (.leaf (2126202289320379:ℤ)) (.branch 142 (.leaf (2246190629102375:ℤ)) (.leaf (2309773558686332:ℤ))))) (.branch 155 (.branch 150 (.leaf (2375914551589844:ℤ)) (.leaf (2444747743077334:ℤ))) (.branch 160 (.leaf (2534793635049304:ℤ)) (.branch 162 (.leaf (2629569788181030:ℤ)) (.leaf (2668876625644495:ℤ)))))) (.branch 184 (.branch 173 (.branch 171 (.leaf (2750004681186124:ℤ)) (.leaf (2856370790965568:ℤ))) (.branch 176 (.leaf (2900538466506606:ℤ)) (.branch 180 (.leaf (2968608994318021:ℤ)) (.leaf (3062911386597926:ℤ))))) (.branch 194 (.branch 187 (.leaf (3161477446691822:ℤ)) (.branch 191 (.leaf (3238350707450152:ℤ)) (.leaf (3344994649515970:ℤ)))) (.branch 197 (.leaf (3428243068074551:ℤ)) (.branch 200 (.leaf (3514432026129834:ℤ)) (.leaf (3603696705812040:ℤ))))))), (.branch 166 (.branch 146 (.branch 130 (.branch 122 (.leaf (1884534056646949:ℤ)) (.leaf (2011784554196763:ℤ))) (.branch 138 (.leaf (2122482672124185:ℤ)) (.branch 142 (.leaf (2241976898770611:ℤ)) (.leaf (2305309369970286:ℤ))))) (.branch 155 (.branch 150 (.leaf (2371199995311099:ℤ)) (.leaf (2439785079924262:ℤ))) (.branch 160 (.leaf (2529527936319427:ℤ)) (.branch 162 (.leaf (2624014530700421:ℤ)) (.leaf (2663210879414868:ℤ)))))) (.branch 184 (.branch 173 (.branch 171 (.leaf (2744129950477188:ℤ)) (.leaf (2850263507050145:ℤ))) (.branch 176 (.leaf (2894349251709142:ℤ)) (.branch 180 (.leaf (2962311161364209:ℤ)) (.leaf (3056499943887863:ℤ))))) (.branch 194 (.branch 187 (.leaf (3154995226977722:ℤ)) (.branch 191 (.leaf (3231848832180874:ℤ)) (.leaf (3338519228580808:ℤ)))) (.branch 197 (.leaf (3421833221767519:ℤ)) (.branch 200 (.leaf (3508132945292671:ℤ)) (.leaf (3597559619521690:ℤ))))))), (.branch 166 (.branch 146 (.branch 130 (.branch 122 (.leaf (1892719642062801:ℤ)) (.leaf (2022347092927252:ℤ))) (.branch 138 (.leaf (2135329513860561:ℤ)) (.branch 142 (.leaf (2257507737423125:ℤ)) (.leaf (2322352001256365:ℤ))))) (.branch 155 (.branch 150 (.leaf (2389879596733876:ℤ)) (.leaf (2460236780988540:ℤ))) (.branch 160 (.leaf (2552401351106564:ℤ)) (.branch 162 (.leaf (2649560990025054:ℤ)) (.leaf (2689902619185541:ℤ)))))) (.branch 184 (.branch 173 (.branch 171 (.leaf (2773252382118292:ℤ)) (.leaf (2882706959303139:ℤ))) (.branch 176 (.leaf (2928215699337729:ℤ)) (.branch 180 (.leaf (2998420439225796:ℤ)) (.leaf (3095814589926141:ℤ))))) (.branch 194 (.branch 187 (.leaf (3197779957266598:ℤ)) (.branch 191 (.leaf (3277423401679125:ℤ)) (.leaf (3388082976245281:ℤ)))) (.branch 197 (.leaf (3474605451817665:ℤ)) (.branch 200 (.leaf (3564312770307172:ℤ)) (.leaf (3657359223773372:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 16 17) 8000 (endpointMeanRuns 16 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 16 17, EndpointRunConditions (endpointMeanCutoff 16 17) (endpointMeanBox 16 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 16 17 h) (endpointMeanCornerA 16 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 17, endpointJoint24Q (endpointMeanCornerK 16 17 h) (endpointMeanCornerA 16 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 16 17, endpointRunWeightQ (endpointMeanCutoff 16 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 16 17) = (436945369/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 16 17 h = (logRoundedQ ((endpointMeanCutoff 16 17:ℚ)/200)).2+(436945369/1000000000000000:ℚ)+((endpointMeanRuns 16 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 16 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 16 17) r*endpointJoint24Q (endpointMeanCornerK 16 17 h) (endpointMeanCornerA 16 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 16 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 16 17 h≤endpointMeanCorner 16 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 16 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint16_17

namespace EndpointAnalyticJoint16_18
private noncomputable def weights : IntegerLookupTree := (.branch 1414 (.branch 1154 (.branch 1004 (.leaf (83509960900000:ℤ)) (.branch 1068 (.leaf (3575781700000:ℤ)) (.leaf (4233022000000:ℤ)))) (.branch 1255 (.leaf (4152854300000:ℤ)) (.branch 1321 (.leaf (2188557300000:ℤ)) (.leaf (2666350400000:ℤ))))) (.branch 1825 (.branch 1521 (.leaf (2493054500000:ℤ)) (.branch 1673 (.leaf (2754992100000:ℤ)) (.leaf (1945224400000:ℤ)))) (.branch 2641 (.branch 2181 (.leaf (2976075700000:ℤ)) (.leaf (1564484000000:ℤ))) (.branch 3345 (.leaf (702013200000:ℤ)) (.leaf (453108300000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.branch 130 (.leaf (1887220320164453:ℤ)) (.branch 138 (.leaf (2126202289320379:ℤ)) (.leaf (2246190629102375:ℤ)))) (.branch 155 (.leaf (2375914551589844:ℤ)) (.branch 160 (.leaf (2534793635049304:ℤ)) (.leaf (2629569788181030:ℤ))))) (.branch 180 (.branch 171 (.leaf (2750004681186124:ℤ)) (.branch 176 (.leaf (2856370790965568:ℤ)) (.leaf (2968608994318021:ℤ)))) (.branch 194 (.branch 187 (.leaf (3062911386597926:ℤ)) (.leaf (3238350707450152:ℤ))) (.branch 200 (.leaf (3428243068074551:ℤ)) (.leaf (3603696705812040:ℤ)))))), (.branch 166 (.branch 146 (.branch 130 (.leaf (1895111199573927:ℤ)) (.branch 138 (.leaf (2138562660144395:ℤ)) (.leaf (2261119251551008:ℤ)))) (.branch 155 (.leaf (2393851761220364:ℤ)) (.branch 160 (.leaf (2556731214864947:ℤ)) (.leaf (2654053372899186:ℤ))))) (.branch 180 (.branch 171 (.leaf (2777890003660246:ℤ)) (.branch 176 (.leaf (2887411141171692:ℤ)) (.leaf (3003127484626719:ℤ)))) (.branch 194 (.branch 187 (.leaf (3100467453125644:ℤ)) (.leaf (3281829551651896:ℤ))) (.branch 200 (.leaf (3478517237581315:ℤ)) (.leaf (3660591095378273:ℤ)))))), (.branch 166 (.branch 146 (.branch 130 (.leaf (1892719642062801:ℤ)) (.branch 138 (.leaf (2135329513860561:ℤ)) (.leaf (2257507737423125:ℤ)))) (.branch 155 (.leaf (2389879596733876:ℤ)) (.branch 160 (.leaf (2552401351106564:ℤ)) (.leaf (2649560990025054:ℤ))))) (.branch 180 (.branch 171 (.leaf (2773252382118292:ℤ)) (.branch 176 (.leaf (2882706959303139:ℤ)) (.leaf (2998420439225796:ℤ)))) (.branch 194 (.branch 187 (.leaf (3095814589926141:ℤ)) (.leaf (3277423401679125:ℤ))) (.branch 200 (.leaf (3474605451817665:ℤ)) (.leaf (3657359223773372:ℤ)))))), (.branch 166 (.branch 146 (.branch 130 (.leaf (1900940782054256:ℤ)) (.branch 138 (.leaf (2148254114225907:ℤ)) (.leaf (2273146162799382:ℤ)))) (.branch 155 (.leaf (2408706350446632:ℤ)) (.branch 160 (.leaf (2575481600179461:ℤ)) (.leaf (2675356160466337:ℤ))))) (.branch 180 (.branch 171 (.leaf (2802683879306583:ℤ)) (.branch 176 (.leaf (2915519702883579:ℤ)) (.leaf (3034969873396645:ℤ)))) (.branch 194 (.branch 187 (.leaf (3135634925943639:ℤ)) (.leaf (3323640650180267:ℤ))) (.branch 200 (.leaf (3528191546274402:ℤ)) (.leaf (3718152833141528:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 16 18) 8000 (endpointMeanRuns 16 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 16 18, EndpointRunConditions (endpointMeanCutoff 16 18) (endpointMeanBox 16 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 16 18 h) (endpointMeanCornerA 16 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 16 18, endpointJoint24Q (endpointMeanCornerK 16 18 h) (endpointMeanCornerA 16 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 16 18, endpointRunWeightQ (endpointMeanCutoff 16 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 16 18) = (435611957/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 16 18 h = (logRoundedQ ((endpointMeanCutoff 16 18:ℚ)/200)).2+(435611957/1000000000000000:ℚ)+((endpointMeanRuns 16 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 16 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 16 18) r*endpointJoint24Q (endpointMeanCornerK 16 18 h) (endpointMeanCornerA 16 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 16 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 16 18 h≤endpointMeanCorner 16 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 16 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint16_18

namespace EndpointAnalyticJoint17_03
private noncomputable def weights : IntegerLookupTree := (.branch 1481 (.branch 977 (.leaf (133852546600000:ℤ)) (.leaf (35922251200000:ℤ))) (.branch 2124 (.leaf (13072752600000:ℤ)) (.leaf (12739977800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.leaf (1780957953633488:ℤ)) (.leaf (2140526872640973:ℤ))) (.branch 200 (.leaf (2391153068045309:ℤ)) (.leaf (2901529529899989:ℤ)))), (.branch 166 (.branch 146 (.leaf (1781287848462510:ℤ)) (.leaf (2141244774778693:ℤ))) (.branch 200 (.leaf (2392232042803016:ℤ)) (.leaf (2903574386813572:ℤ)))), (.branch 166 (.branch 146 (.leaf (1782132684603580:ℤ)) (.leaf (2143405590520484:ℤ))) (.branch 200 (.leaf (2395810383109428:ℤ)) (.leaf (2911616112708216:ℤ)))), (.branch 166 (.branch 146 (.leaf (1782475489491264:ℤ)) (.leaf (2144155576867822:ℤ))) (.branch 200 (.leaf (2396941825794639:ℤ)) (.leaf (2913777270867115:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 17 3) 8000 (endpointMeanRuns 17 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 17 3, EndpointRunConditions (endpointMeanCutoff 17 3) (endpointMeanBox 17 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 17 3 h) (endpointMeanCornerA 17 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 3, endpointJoint24Q (endpointMeanCornerK 17 3 h) (endpointMeanCornerA 17 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 17 3, endpointRunWeightQ (endpointMeanCutoff 17 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 17 3) = (455325749/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 17 3 h = (logRoundedQ ((endpointMeanCutoff 17 3:ℚ)/200)).2+(455325749/1000000000000000:ℚ)+((endpointMeanRuns 17 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 17 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 17 3) r*endpointJoint24Q (endpointMeanCornerK 17 3 h) (endpointMeanCornerA 17 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 17 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 17 3 h≤endpointMeanCorner 17 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 17 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint17_03

namespace EndpointAnalyticJoint17_04
private noncomputable def weights : IntegerLookupTree := (.branch 1481 (.branch 977 (.leaf (131491962000000:ℤ)) (.leaf (35796997700000:ℤ))) (.branch 2124 (.leaf (13034722600000:ℤ)) (.leaf (12708108800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.leaf (1781287848462510:ℤ)) (.leaf (2141244774778693:ℤ))) (.branch 200 (.leaf (2392232042803016:ℤ)) (.leaf (2903574386813572:ℤ)))), (.branch 166 (.branch 146 (.leaf (1789024977851270:ℤ)) (.leaf (2158112858036351:ℤ))) (.branch 200 (.leaf (2417619912690180:ℤ)) (.leaf (2951838381746290:ℤ)))), (.branch 166 (.branch 146 (.leaf (1782475489491264:ℤ)) (.leaf (2144155576867822:ℤ))) (.branch 200 (.leaf (2396941825794639:ℤ)) (.leaf (2913777270867115:ℤ)))), (.branch 166 (.branch 146 (.leaf (1790516101615121:ℤ)) (.leaf (2161780646608761:ℤ))) (.branch 200 (.leaf (2423571083890549:ℤ)) (.leaf (2964809670659031:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 17 4) 8000 (endpointMeanRuns 17 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 17 4, EndpointRunConditions (endpointMeanCutoff 17 4) (endpointMeanBox 17 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 17 4 h) (endpointMeanCornerA 17 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 4, endpointJoint24Q (endpointMeanCornerK 17 4 h) (endpointMeanCornerA 17 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 17 4, endpointRunWeightQ (endpointMeanCutoff 17 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 17 4) = (1818167/4000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 17 4 h = (logRoundedQ ((endpointMeanCutoff 17 4:ℚ)/200)).2+(1818167/4000000000000:ℚ)+((endpointMeanRuns 17 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 17 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 17 4) r*endpointJoint24Q (endpointMeanCornerK 17 4 h) (endpointMeanCornerA 17 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 17 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 17 4 h≤endpointMeanCorner 17 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 17 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint17_04

namespace EndpointAnalyticJoint17_05
private noncomputable def weights : IntegerLookupTree := (.branch 1481 (.branch 977 (.leaf (126891939200000:ℤ)) (.leaf (35549021200000:ℤ))) (.branch 2124 (.leaf (12959430800000:ℤ)) (.leaf (12645014600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.leaf (1789024977851270:ℤ)) (.leaf (2158112858036351:ℤ))) (.branch 200 (.leaf (2417619912690180:ℤ)) (.leaf (2951838381746290:ℤ)))), (.branch 166 (.branch 146 (.leaf (1796795713920293:ℤ)) (.leaf (2175113822987941:ℤ))) (.branch 200 (.leaf (2443277214608132:ℤ)) (.leaf (3000904633792675:ℤ)))), (.branch 166 (.branch 146 (.leaf (1790516101615121:ℤ)) (.leaf (2161780646608761:ℤ))) (.branch 200 (.leaf (2423571083890549:ℤ)) (.leaf (2964809670659031:ℤ)))), (.branch 166 (.branch 146 (.leaf (1798592984332151:ℤ)) (.leaf (2179550595334575:ℤ))) (.branch 200 (.leaf (2450496184538458:ℤ)) (.leaf (3016735860739775:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 17 5) 8000 (endpointMeanRuns 17 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 17 5, EndpointRunConditions (endpointMeanCutoff 17 5) (endpointMeanBox 17 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 17 5 h) (endpointMeanCornerA 17 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 5, endpointJoint24Q (endpointMeanCornerK 17 5 h) (endpointMeanCornerA 17 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 17 5, endpointRunWeightQ (endpointMeanCutoff 17 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 17 5) = (452989593/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 17 5 h = (logRoundedQ ((endpointMeanCutoff 17 5:ℚ)/200)).2+(452989593/1000000000000000:ℚ)+((endpointMeanRuns 17 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 17 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 17 5) r*endpointJoint24Q (endpointMeanCornerK 17 5 h) (endpointMeanCornerA 17 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 17 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 17 5 h≤endpointMeanCorner 17 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 17 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint17_05

namespace EndpointAnalyticJoint17_06
private noncomputable def weights : IntegerLookupTree := (.branch 1481 (.branch 977 (.leaf (122448528900000:ℤ)) (.leaf (35304343800000:ℤ))) (.branch 2124 (.leaf (12885140700000:ℤ)) (.leaf (12582759700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.leaf (1796795713920293:ℤ)) (.leaf (2175113822987941:ℤ))) (.branch 200 (.leaf (2443277214608132:ℤ)) (.leaf (3000904633792675:ℤ)))), (.branch 166 (.branch 146 (.leaf (1804600202642187:ℤ)) (.leaf (2192248716435533:ℤ))) (.branch 200 (.leaf (2469206807938913:ℤ)) (.leaf (3050786478286384:ℤ)))), (.branch 166 (.branch 146 (.leaf (1798592984332151:ℤ)) (.leaf (2179550595334575:ℤ))) (.branch 200 (.leaf (2450496184538458:ℤ)) (.leaf (3016735860739775:ℤ)))), (.branch 166 (.branch 146 (.leaf (1806706301256259:ℤ)) (.leaf (2197466613958000:ℤ))) (.branch 200 (.leaf (2477720414454629:ℤ)) (.leaf (3069571495107281:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 17 6) 8000 (endpointMeanRuns 17 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 17 6, EndpointRunConditions (endpointMeanCutoff 17 6) (endpointMeanBox 17 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 17 6 h) (endpointMeanCornerA 17 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 6, endpointJoint24Q (endpointMeanCornerK 17 6 h) (endpointMeanCornerA 17 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 17 6, endpointRunWeightQ (endpointMeanCutoff 17 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 17 6) = (90291617/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 17 6 h = (logRoundedQ ((endpointMeanCutoff 17 6:ℚ)/200)).2+(90291617/200000000000000:ℚ)+((endpointMeanRuns 17 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 17 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 17 6) r*endpointJoint24Q (endpointMeanCornerK 17 6 h) (endpointMeanCornerA 17 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 17 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 17 6 h≤endpointMeanCorner 17 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 17 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint17_06

namespace EndpointAnalyticJoint17_07
private noncomputable def weights : IntegerLookupTree := (.branch 1150 (.branch 977 (.leaf (118156045000000:ℤ)) (.leaf (11904843400000:ℤ))) (.branch 1481 (.leaf (15432456800000:ℤ)) (.branch 2124 (.leaf (12811826000000:ℤ)) (.leaf (12521322300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.leaf (1804600202642187:ℤ)) (.leaf (2192248716435533:ℤ))) (.branch 185 (.leaf (2469206807938913:ℤ)) (.branch 200 (.leaf (2774643280721585:ℤ)) (.leaf (3050786478286384:ℤ))))), (.branch 166 (.branch 146 (.leaf (1812438590623603:ℤ)) (.leaf (2209518593427599:ℤ))) (.branch 185 (.leaf (2495411582410126:ℤ)) (.branch 200 (.leaf (2812765656733709:ℤ)) (.leaf (3101497472224587:ℤ))))), (.branch 166 (.branch 146 (.leaf (1806706301256259:ℤ)) (.leaf (2197466613958000:ℤ))) (.branch 185 (.leaf (2477720414454629:ℤ)) (.branch 200 (.leaf (2787952935678920:ℤ)) (.leaf (3069571495107281:ℤ))))), (.branch 166 (.branch 146 (.leaf (1814856216739400:ℤ)) (.leaf (2215529903181158:ℤ))) (.branch 185 (.leaf (2505247096869686:ℤ)) (.branch 200 (.leaf (2828190960092714:ℤ)) (.leaf (3123332501926293:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 17 7) 8000 (endpointMeanRuns 17 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 17 7, EndpointRunConditions (endpointMeanCutoff 17 7) (endpointMeanBox 17 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 17 7 h) (endpointMeanCornerA 17 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 7, endpointJoint24Q (endpointMeanCornerK 17 7 h) (endpointMeanCornerA 17 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 17 7, endpointRunWeightQ (endpointMeanCutoff 17 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 17 7) = (224973343/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 17 7 h = (logRoundedQ ((endpointMeanCutoff 17 7:ℚ)/200)).2+(224973343/500000000000000:ℚ)+((endpointMeanRuns 17 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 17 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 17 7) r*endpointJoint24Q (endpointMeanCornerK 17 7 h) (endpointMeanCornerA 17 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 17 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 17 7 h≤endpointMeanCorner 17 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 17 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint17_07

namespace EndpointAnalyticJoint17_08
private noncomputable def weights : IntegerLookupTree := (.branch 1481 (.branch 977 (.leaf (114009033500000:ℤ)) (.branch 1150 (.leaf (11820322200000:ℤ)) (.leaf (15333408900000:ℤ)))) (.branch 2124 (.leaf (12739461400000:ℤ)) (.branch 3257 (.leaf (3983160800000:ℤ)) (.leaf (596827300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 130 (.leaf (1812438590623603:ℤ)) (.branch 146 (.leaf (2010283965303452:ℤ)) (.leaf (2209518593427599:ℤ)))) (.branch 185 (.leaf (2495411582410126:ℤ)) (.branch 200 (.leaf (2812765656733709:ℤ)) (.leaf (3101497472224587:ℤ))))), (.branch 166 (.branch 130 (.leaf (1820311025107977:ℤ)) (.branch 146 (.leaf (2022451697123652:ℤ)) (.leaf (2226924517323965:ℤ)))) (.branch 185 (.leaf (2521894458416970:ℤ)) (.branch 200 (.leaf (2851411817393375:ℤ)) (.leaf (3153051397952514:ℤ))))), (.branch 166 (.branch 130 (.leaf (1814856216739400:ℤ)) (.branch 146 (.leaf (2014256870340040:ℤ)) (.leaf (2215529903181158:ℤ)))) (.branch 185 (.leaf (2505247096869686:ℤ)) (.branch 200 (.leaf (2828190960092714:ℤ)) (.leaf (3123332501926293:ℤ))))), (.branch 166 (.branch 130 (.leaf (1823042895874906:ℤ)) (.branch 146 (.leaf (2026948823222064:ℤ)) (.leaf (2233741673575985:ℤ)))) (.branch 185 (.leaf (2533079591934290:ℤ)) (.branch 200 (.leaf (2869009732692035:ℤ)) (.leaf (3178035088330212:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 17 8) 8000 (endpointMeanRuns 17 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 17 8, EndpointRunConditions (endpointMeanCutoff 17 8) (endpointMeanBox 17 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 17 8 h) (endpointMeanCornerA 17 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 8, endpointJoint24Q (endpointMeanCornerK 17 8 h) (endpointMeanCornerA 17 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 17 8, endpointRunWeightQ (endpointMeanCutoff 17 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 17 8) = (448454873/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 17 8 h = (logRoundedQ ((endpointMeanCutoff 17 8:ℚ)/200)).2+(448454873/1000000000000000:ℚ)+((endpointMeanRuns 17 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 17 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 17 8) r*endpointJoint24Q (endpointMeanCornerK 17 8 h) (endpointMeanCornerA 17 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 17 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 17 8 h≤endpointMeanCorner 17 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 17 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint17_08

namespace EndpointAnalyticJoint17_09
private noncomputable def weights : IntegerLookupTree := (.branch 1481 (.branch 977 (.leaf (110002261600000:ℤ)) (.branch 1150 (.leaf (11736882300000:ℤ)) (.leaf (15235628100000:ℤ)))) (.branch 2124 (.leaf (12668022600000:ℤ)) (.branch 3257 (.leaf (3963819900000:ℤ)) (.leaf (594318700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 130 (.leaf (1820311025107977:ℤ)) (.branch 146 (.leaf (2022451697123652:ℤ)) (.leaf (2226924517323965:ℤ)))) (.branch 185 (.leaf (2521894458416970:ℤ)) (.branch 200 (.leaf (2851411817393375:ℤ)) (.leaf (3153051397952514:ℤ))))), (.branch 166 (.branch 130 (.leaf (1828217653978324:ℤ)) (.branch 146 (.leaf (2034693077095159:ℤ)) (.leaf (2244467559861274:ℤ)))) (.branch 185 (.leaf (2548658387347724:ℤ)) (.branch 200 (.leaf (2890588959270809:ℤ)) (.leaf (3205462266909238:ℤ))))), (.branch 166 (.branch 130 (.leaf (1823042895874906:ℤ)) (.branch 146 (.leaf (2026948823222064:ℤ)) (.leaf (2233741673575985:ℤ)))) (.branch 185 (.leaf (2533079591934290:ℤ)) (.branch 200 (.leaf (2869009732692035:ℤ)) (.leaf (3178035088330212:ℤ))))), (.branch 166 (.branch 130 (.leaf (1831266504500831:ℤ)) (.branch 146 (.leaf (2039720748857478:ℤ)) (.leaf (2252103145665402:ℤ)))) (.branch 185 (.leaf (2561221297129295:ℤ)) (.branch 200 (.leaf (2910417635311223:ℤ)) (.leaf (3233695745306967:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 17 9) 8000 (endpointMeanRuns 17 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 17 9, EndpointRunConditions (endpointMeanCutoff 17 9) (endpointMeanBox 17 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 17 9 h) (endpointMeanCornerA 17 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 9, endpointJoint24Q (endpointMeanCornerK 17 9 h) (endpointMeanCornerA 17 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 17 9, endpointRunWeightQ (endpointMeanCutoff 17 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 17 9) = (223491073/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 17 9 h = (logRoundedQ ((endpointMeanCutoff 17 9:ℚ)/200)).2+(223491073/500000000000000:ℚ)+((endpointMeanRuns 17 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 17 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 17 9) r*endpointJoint24Q (endpointMeanCornerK 17 9 h) (endpointMeanCornerA 17 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 17 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 17 9 h≤endpointMeanCorner 17 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 17 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint17_09

namespace EndpointAnalyticJoint17_10
private noncomputable def weights : IntegerLookupTree := (.branch 1481 (.branch 977 (.leaf (106130707300000:ℤ)) (.branch 1150 (.leaf (11654496300000:ℤ)) (.leaf (15139082500000:ℤ)))) (.branch 2124 (.leaf (12597486200000:ℤ)) (.branch 3257 (.leaf (3944723200000:ℤ)) (.leaf (591841800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 130 (.leaf (1828217653978324:ℤ)) (.branch 146 (.leaf (2034693077095159:ℤ)) (.leaf (2244467559861274:ℤ)))) (.branch 185 (.leaf (2548658387347724:ℤ)) (.branch 200 (.leaf (2890588959270809:ℤ)) (.leaf (3205462266909238:ℤ))))), (.branch 166 (.branch 130 (.leaf (1836158625759979:ℤ)) (.branch 146 (.leaf (2047008550991292:ℤ)) (.leaf (2262148801219016:ℤ)))) (.branch 185 (.leaf (2575706351912648:ℤ)) (.branch 200 (.leaf (2930304377813974:ℤ)) (.leaf (3258744323435751:ℤ))))), (.branch 166 (.branch 130 (.leaf (1831266504500831:ℤ)) (.branch 146 (.leaf (2039720748857478:ℤ)) (.leaf (2252103145665402:ℤ)))) (.branch 185 (.leaf (2561221297129295:ℤ)) (.branch 200 (.leaf (2910417635311223:ℤ)) (.leaf (3233695745306967:ℤ))))), (.branch 166 (.branch 130 (.leaf (1839527209203311:ℤ)) (.branch 146 (.leaf (2052573151159385:ℤ)) (.leaf (2270615550005082:ℤ)))) (.branch 185 (.leaf (2589675647680496:ℤ)) (.branch 200 (.leaf (2952423170758141:ℤ)) (.leaf (3290331252670508:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 17 10) 8000 (endpointMeanRuns 17 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 17 10, EndpointRunConditions (endpointMeanCutoff 17 10) (endpointMeanBox 17 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 17 10 h) (endpointMeanCornerA 17 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 10, endpointJoint24Q (endpointMeanCornerK 17 10 h) (endpointMeanCornerA 17 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 17 10, endpointRunWeightQ (endpointMeanCutoff 17 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 17 10) = (222764011/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 17 10 h = (logRoundedQ ((endpointMeanCutoff 17 10:ℚ)/200)).2+(222764011/500000000000000:ℚ)+((endpointMeanRuns 17 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 17 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 17 10) r*endpointJoint24Q (endpointMeanCornerK 17 10 h) (endpointMeanCornerA 17 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 17 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 17 10 h≤endpointMeanCorner 17 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 17 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint17_10

namespace EndpointAnalyticJoint17_11
private noncomputable def weights : IntegerLookupTree := (.branch 1481 (.branch 1150 (.branch 977 (.leaf (102389548600000:ℤ)) (.leaf (11573138200000:ℤ))) (.branch 1286 (.leaf (6248971700000:ℤ)) (.leaf (6585130000000:ℤ)))) (.branch 2124 (.branch 1745 (.leaf (5614975600000:ℤ)) (.leaf (4167993900000:ℤ))) (.branch 3257 (.leaf (3925864800000:ℤ)) (.leaf (589395900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.branch 130 (.leaf (1836158625759979:ℤ)) (.leaf (2047008550991292:ℤ))) (.branch 156 (.leaf (2262148801219016:ℤ)) (.leaf (2412112477033992:ℤ)))) (.branch 185 (.branch 176 (.leaf (2575706351912648:ℤ)) (.leaf (2754606363167890:ℤ))) (.branch 200 (.leaf (2930304377813974:ℤ)) (.leaf (3258744323435751:ℤ))))), (.branch 166 (.branch 146 (.branch 130 (.leaf (1844134089623417:ℤ)) (.leaf (2059398567283519:ℤ))) (.branch 156 (.leaf (2279969330085978:ℤ)) (.leaf (2434252038336029:ℤ)))) (.branch 185 (.branch 176 (.leaf (2603041366476405:ℤ)) (.leaf (2788183810353116:ℤ))) (.branch 200 (.leaf (2970565468707059:ℤ)) (.leaf (3312912048646309:ℤ))))), (.branch 166 (.branch 146 (.branch 130 (.leaf (1839527209203311:ℤ)) (.leaf (2052573151159385:ℤ))) (.branch 156 (.leaf (2270615550005082:ℤ)) (.leaf (2423017536866686:ℤ)))) (.branch 185 (.branch 176 (.leaf (2589675647680496:ℤ)) (.leaf (2772424495598764:ℤ))) (.branch 200 (.leaf (2952423170758141:ℤ)) (.leaf (3290331252670508:ℤ))))), (.branch 166 (.branch 146 (.branch 130 (.leaf (1847825177319945:ℤ)) (.leaf (2065506537216063:ℤ))) (.branch 156 (.leaf (2289280127265917:ℤ)) (.leaf (2446260122312220:ℤ)))) (.branch 185 (.branch 176 (.leaf (2618446116977937:ℤ)) (.leaf (2807864486822666:ℤ))) (.branch 200 (.leaf (2995034964560136:ℤ)) (.leaf (3347958684119353:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 17 11) 8000 (endpointMeanRuns 17 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 17 11, EndpointRunConditions (endpointMeanCutoff 17 11) (endpointMeanBox 17 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 17 11 h) (endpointMeanCornerA 17 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 11, endpointJoint24Q (endpointMeanCornerK 17 11 h) (endpointMeanCornerA 17 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 17 11, endpointRunWeightQ (endpointMeanCutoff 17 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 17 11) = (444092037/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 17 11 h = (logRoundedQ ((endpointMeanCutoff 17 11:ℚ)/200)).2+(444092037/1000000000000000:ℚ)+((endpointMeanRuns 17 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 17 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 17 11) r*endpointJoint24Q (endpointMeanCornerK 17 11 h) (endpointMeanCornerA 17 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 17 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 17 11 h≤endpointMeanCorner 17 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 17 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint17_11

namespace EndpointAnalyticJoint17_12
private noncomputable def weights : IntegerLookupTree := (.branch 1396 (.branch 1051 (.branch 977 (.leaf (98774155200000:ℤ)) (.leaf (4834125300000:ℤ))) (.branch 1150 (.leaf (5575413300000:ℤ)) (.branch 1286 (.leaf (6208789200000:ℤ)) (.leaf (3737593200000:ℤ))))) (.branch 2124 (.branch 1481 (.leaf (2273489900000:ℤ)) (.branch 1745 (.leaf (5583360400000:ℤ)) (.leaf (4146247100000:ℤ)))) (.branch 2571 (.leaf (1908552700000:ℤ)) (.branch 3257 (.leaf (886833600000:ℤ)) (.leaf (586980000000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 138 (.branch 130 (.leaf (1844134089623417:ℤ)) (.leaf (2059398567283519:ℤ))) (.branch 146 (.leaf (2165910778326561:ℤ)) (.branch 156 (.leaf (2279969330085978:ℤ)) (.leaf (2434252038336029:ℤ))))) (.branch 185 (.branch 170 (.leaf (2603041366476405:ℤ)) (.branch 176 (.leaf (2675022910691191:ℤ)) (.leaf (2788183810353116:ℤ)))) (.branch 193 (.leaf (2970565468707059:ℤ)) (.branch 200 (.leaf (3146729033190864:ℤ)) (.leaf (3312912048646309:ℤ)))))), (.branch 166 (.branch 138 (.branch 130 (.leaf (1852144195387041:ℤ)) (.leaf (2071863577157794:ℤ))) (.branch 146 (.leaf (2180914684411573:ℤ)) (.branch 156 (.leaf (2297930243727329:ℤ)) (.leaf (2456594807481530:ℤ))))) (.branch 185 (.branch 170 (.leaf (2630666477393982:ℤ)) (.branch 176 (.leaf (2705051922554556:ℤ)) (.leaf (2822170551938645:ℤ)))) (.branch 193 (.leaf (3011379729247696:ℤ)) (.branch 200 (.leaf (3194648726708954:ℤ)) (.leaf (3367980164364152:ℤ)))))), (.branch 166 (.branch 138 (.branch 130 (.leaf (1847825177319945:ℤ)) (.leaf (2065506537216063:ℤ))) (.branch 146 (.leaf (2173471154511012:ℤ)) (.branch 156 (.leaf (2289280127265917:ℤ)) (.leaf (2446260122312220:ℤ))))) (.branch 185 (.branch 170 (.leaf (2618446116977937:ℤ)) (.branch 176 (.leaf (2692020913673970:ℤ)) (.leaf (2807864486822666:ℤ)))) (.branch 193 (.leaf (2995034964560136:ℤ)) (.branch 200 (.leaf (3176379243367223:ℤ)) (.leaf (3347958684119353:ℤ)))))), (.branch 166 (.branch 138 (.branch 130 (.leaf (1856160576943174:ℤ)) (.leaf (2078521417310989:ℤ))) (.branch 146 (.leaf (2189163027534816:ℤ)) (.branch 156 (.leaf (2308098128317203:ℤ)) (.leaf (2469725660241577:ℤ))))) (.branch 185 (.branch 170 (.leaf (2647536216999922:ℤ)) (.branch 176 (.leaf (2723678062211612:ℤ)) (.leaf (2843757508590749:ℤ)))) (.branch 193 (.leaf (3038261766735260:ℤ)) (.branch 200 (.leaf (3227271706836964:ℤ)) (.leaf (3406595412383745:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 17 12) 8000 (endpointMeanRuns 17 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 17 12, EndpointRunConditions (endpointMeanCutoff 17 12) (endpointMeanBox 17 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 17 12 h) (endpointMeanCornerA 17 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 12, endpointJoint24Q (endpointMeanCornerK 17 12 h) (endpointMeanCornerA 17 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 17 12, endpointRunWeightQ (endpointMeanCutoff 17 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 17 12) = (88534749/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 17 12 h = (logRoundedQ ((endpointMeanCutoff 17 12:ℚ)/200)).2+(88534749/200000000000000:ℚ)+((endpointMeanRuns 17 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 17 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 17 12) r*endpointJoint24Q (endpointMeanCornerK 17 12 h) (endpointMeanCornerA 17 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 17 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 17 12 h≤endpointMeanCorner 17 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 17 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint17_12

namespace EndpointAnalyticJoint17_13
private noncomputable def weights : IntegerLookupTree := (.branch 1396 (.branch 1111 (.branch 1008 (.branch 977 (.leaf (95280078600000:ℤ)) (.leaf (1988531500000:ℤ))) (.branch 1051 (.leaf (2604480600000:ℤ)) (.leaf (3339761100000:ℤ)))) (.branch 1222 (.branch 1150 (.leaf (1916734500000:ℤ)) (.leaf (3265703400000:ℤ))) (.branch 1286 (.leaf (2493258600000:ℤ)) (.leaf (3714878200000:ℤ))))) (.branch 1954 (.branch 1629 (.branch 1481 (.leaf (2260151300000:ℤ)) (.leaf (3204636500000:ℤ))) (.branch 1745 (.leaf (1811207600000:ℤ)) (.leaf (2414792700000:ℤ)))) (.branch 2571 (.branch 2124 (.leaf (1223312100000:ℤ)) (.leaf (1899411500000:ℤ))) (.branch 3257 (.leaf (882893300000:ℤ)) (.branch 4441 (.leaf (230172600000:ℤ)) (.leaf (23293100000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.branch 130 (.branch 122 (.leaf (1852144195387041:ℤ)) (.leaf (1970083197447320:ℤ))) (.branch 138 (.leaf (2071863577157794:ℤ)) (.leaf (2180914684411573:ℤ)))) (.branch 156 (.branch 150 (.leaf (2297930243727329:ℤ)) (.leaf (2359664330660193:ℤ))) (.branch 160 (.leaf (2456594807481530:ℤ)) (.leaf (2524268189738877:ℤ))))) (.branch 185 (.branch 176 (.branch 170 (.leaf (2630666477393982:ℤ)) (.leaf (2705051922554556:ℤ))) (.branch 180 (.leaf (2822170551938645:ℤ)) (.leaf (2904171038560340:ℤ)))) (.branch 193 (.branch 188 (.leaf (3011379729247696:ℤ)) (.leaf (3078352115975525:ℤ))) (.branch 197 (.leaf (3194648726708954:ℤ)) (.branch 200 (.leaf (3292130098951901:ℤ)) (.leaf (3367980164364152:ℤ))))))), (.branch 166 (.branch 146 (.branch 130 (.branch 122 (.leaf (1860189093519995:ℤ)) (.leaf (1980426790170463:ℤ))) (.branch 138 (.leaf (2084404034530986:ℤ)) (.leaf (2196022527002220:ℤ)))) (.branch 156 (.branch 150 (.leaf (2316032648052169:ℤ)) (.leaf (2379444412889484:ℤ))) (.branch 160 (.leaf (2479142649612585:ℤ)) (.leaf (2548843554653651:ℤ))))) (.branch 185 (.branch 176 (.branch 170 (.leaf (2658584763350202:ℤ)) (.leaf (2735418031176946:ℤ))) (.branch 180 (.leaf (2856571577044257:ℤ)) (.leaf (2941526333345785:ℤ)))) (.branch 193 (.branch 188 (.leaf (3052754759743091:ℤ)) (.leaf (3122327174922996:ℤ))) (.branch 197 (.leaf (3243298161174760:ℤ)) (.branch 200 (.leaf (3344850818425279:ℤ)) (.leaf (3423963637122621:ℤ))))))), (.branch 166 (.branch 146 (.branch 130 (.branch 122 (.leaf (1856160576943174:ℤ)) (.leaf (1975425408149134:ℤ))) (.branch 138 (.leaf (2078521417310989:ℤ)) (.leaf (2189163027534816:ℤ)))) (.branch 156 (.branch 150 (.leaf (2308098128317203:ℤ)) (.leaf (2370935296609789:ℤ))) (.branch 160 (.leaf (2469725660241577:ℤ)) (.leaf (2538791258106900:ℤ))))) (.branch 185 (.branch 176 (.branch 170 (.leaf (2647536216999922:ℤ)) (.leaf (2723678062211612:ℤ))) (.branch 180 (.leaf (2843757508590749:ℤ)) (.leaf (2927974665758117:ℤ)))) (.branch 193 (.branch 188 (.leaf (3038261766735260:ℤ)) (.leaf (3107261719036758:ℤ))) (.branch 197 (.leaf (3227271706836964:ℤ)) (.branch 200 (.leaf (3328055343479992:ℤ)) (.leaf (3406595412383745:ℤ))))))), (.branch 166 (.branch 146 (.branch 130 (.branch 122 (.leaf (1864533576923695:ℤ)) (.leaf (1986210748781921:ℤ))) (.branch 138 (.leaf (2091618304942970:ℤ)) (.leaf (2204968191631514:ℤ)))) (.branch 156 (.branch 150 (.leaf (2327070814310425:ℤ)) (.leaf (2391686368990311:ℤ))) (.branch 160 (.leaf (2493416289307109:ℤ)) (.leaf (2564639538195457:ℤ))))) (.branch 185 (.branch 176 (.branch 170 (.leaf (2676949498741704:ℤ)) (.leaf (2755707486851740:ℤ))) (.branch 180 (.leaf (2880109352006992:ℤ)) (.leaf (2967498902863112:ℤ)))) (.branch 193 (.branch 188 (.leaf (3082112453588990:ℤ)) (.leaf (3153916715865636:ℤ))) (.branch 197 (.leaf (3278979577611558:ℤ)) (.branch 200 (.leaf (3384175553962630:ℤ)) (.leaf (3466259114462912:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 17 13) 8000 (endpointMeanRuns 17 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 17 13, EndpointRunConditions (endpointMeanCutoff 17 13) (endpointMeanBox 17 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 17 13 h) (endpointMeanCornerA 17 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 13, endpointJoint24Q (endpointMeanCornerK 17 13 h) (endpointMeanCornerA 17 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 17 13, endpointRunWeightQ (endpointMeanCutoff 17 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 17 13) = (220636357/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 17 13 h = (logRoundedQ ((endpointMeanCutoff 17 13:ℚ)/200)).2+(220636357/500000000000000:ℚ)+((endpointMeanRuns 17 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 17 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 17 13) r*endpointJoint24Q (endpointMeanCornerK 17 13 h) (endpointMeanCornerA 17 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 17 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 17 13 h≤endpointMeanCorner 17 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 17 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint17_13

namespace EndpointAnalyticJoint17_14
private noncomputable def weights : IntegerLookupTree := (.branch 1437 (.branch 1150 (.branch 1051 (.branch 977 (.leaf (92457931900000:ℤ)) (.branch 1008 (.leaf (1976746100000:ℤ)) (.leaf (2589368200000:ℤ)))) (.branch 1086 (.leaf (1931720300000:ℤ)) (.branch 1111 (.leaf (1283465100000:ℤ)) (.leaf (1906185700000:ℤ))))) (.branch 1253 (.branch 1192 (.leaf (1894636600000:ℤ)) (.branch 1222 (.leaf (1239548800000:ℤ)) (.leaf (1203633900000:ℤ)))) (.branch 1339 (.branch 1286 (.leaf (1199962100000:ℤ)) (.leaf (1792137100000:ℤ))) (.branch 1396 (.leaf (1718963900000:ℤ)) (.leaf (1095523400000:ℤ)))))) (.branch 1954 (.branch 1576 (.branch 1481 (.leaf (1073352000000:ℤ)) (.branch 1527 (.leaf (1018479500000:ℤ)) (.leaf (979336900000:ℤ)))) (.branch 1745 (.branch 1629 (.leaf (947811800000:ℤ)) (.leaf (1803027200000:ℤ))) (.branch 1844 (.leaf (1187313300000:ℤ)) (.leaf (1046335700000:ℤ))))) (.branch 2571 (.branch 2124 (.leaf (1218217800000:ℤ)) (.branch 2326 (.leaf (955045800000:ℤ)) (.leaf (700296200000:ℤ)))) (.branch 3257 (.branch 2874 (.leaf (465558200000:ℤ)) (.leaf (269931600000:ℤ))) (.branch 4441 (.leaf (229394200000:ℤ)) (.leaf (23221600000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.branch 134 (.branch 122 (.leaf (1860189093519995:ℤ)) (.branch 130 (.leaf (1980426790170463:ℤ)) (.leaf (2084404034530986:ℤ)))) (.branch 138 (.leaf (2139213277221910:ℤ)) (.branch 142 (.leaf (2196022527002220:ℤ)) (.leaf (2254928217947662:ℤ))))) (.branch 156 (.branch 150 (.leaf (2316032648052169:ℤ)) (.branch 153 (.leaf (2379444412889484:ℤ)) (.leaf (2428586555339305:ℤ)))) (.branch 162 (.branch 160 (.leaf (2479142649612585:ℤ)) (.leaf (2548843554653651:ℤ))) (.branch 164 (.leaf (2584714336446669:ℤ)) (.leaf (2621288670617390:ℤ)))))) (.branch 182 (.branch 173 (.branch 168 (.leaf (2658584763350202:ℤ)) (.branch 170 (.leaf (2696621412562688:ℤ)) (.leaf (2735418031176946:ℤ)))) (.branch 178 (.branch 176 (.leaf (2795081947148761:ℤ)) (.leaf (2856571577044257:ℤ))) (.branch 180 (.leaf (2898615379040549:ℤ)) (.leaf (2941526333345785:ℤ))))) (.branch 190 (.branch 185 (.leaf (2985328096165711:ℤ)) (.branch 188 (.leaf (3052754759743091:ℤ)) (.leaf (3122327174922996:ℤ)))) (.branch 197 (.branch 193 (.leaf (3169945480514147:ℤ)) (.leaf (3243298161174760:ℤ))) (.branch 200 (.leaf (3344850818425279:ℤ)) (.leaf (3423963637122621:ℤ))))))), (.branch 166 (.branch 146 (.branch 134 (.branch 122 (.leaf (1868268935145002:ℤ)) (.branch 130 (.leaf (1990824690199289:ℤ)) (.leaf (2097020396067396:ℤ)))) (.branch 138 (.leaf (2153077040683481:ℤ)) (.branch 142 (.leaf (2211235026097485:ℤ)) (.leaf (2271598392760492:ℤ))))) (.branch 156 (.branch 150 (.leaf (2334277657681596:ℤ)) (.branch 153 (.leaf (2399390303300863:ℤ)) (.leaf (2449896579102040:ℤ)))) (.branch 162 (.branch 160 (.leaf (2501897446990475:ℤ)) (.leaf (2573658176460049:ℤ))) (.branch 164 (.leaf (2610619353200399:ℤ)) (.leaf (2648326462709837:ℤ)))))) (.branch 182 (.branch 173 (.branch 168 (.leaf (2686799335702825:ℤ)) (.branch 170 (.leaf (2726058462739149:ℤ)) (.leaf (2766125020706335:ℤ)))) (.branch 178 (.branch 176 (.leaf (2827786879466387:ℤ)) (.leaf (2891391935604934:ℤ))) (.branch 180 (.leaf (2934914711427295:ℤ)) (.leaf (2979362115688595:ℤ))))) (.branch 190 (.branch 185 (.leaf (3024760074241322:ℤ)) (.branch 188 (.leaf (3094698264925305:ℤ)) (.leaf (3166930429001032:ℤ)))) (.branch 197 (.branch 193 (.leaf (3216408669081256:ℤ)) (.leaf (3292688449385779:ℤ))) (.branch 200 (.leaf (3398415816277163:ℤ)) (.leaf (3480877682232817:ℤ))))))), (.branch 166 (.branch 146 (.branch 134 (.branch 122 (.leaf (1864533576923695:ℤ)) (.branch 130 (.leaf (1986210748781921:ℤ)) (.leaf (2091618304942970:ℤ)))) (.branch 138 (.leaf (2147252123125996:ℤ)) (.branch 142 (.leaf (2204968191631514:ℤ)) (.leaf (2264870782676343:ℤ))))) (.branch 156 (.branch 150 (.leaf (2327070814310425:ℤ)) (.branch 153 (.leaf (2391686368990311:ℤ)) (.leaf (2441808598908562:ℤ)))) (.branch 162 (.branch 160 (.leaf (2493416289307109:ℤ)) (.leaf (2564639538195457:ℤ))) (.branch 164 (.leaf (2601326742240278:ℤ)) (.leaf (2638756697727442:ℤ)))))) (.branch 182 (.branch 173 (.branch 168 (.leaf (2676949498741704:ℤ)) (.branch 170 (.leaf (2715925928249257:ℤ)) (.leaf (2755707486851740:ℤ)))) (.branch 178 (.branch 176 (.leaf (2816938322447959:ℤ)) (.leaf (2880109352006992:ℤ))) (.branch 180 (.leaf (2923341873900623:ℤ)) (.leaf (2967498902863112:ℤ))))) (.branch 190 (.branch 185 (.leaf (3012606934605919:ℤ)) (.branch 188 (.leaf (3082112453588990:ℤ)) (.leaf (3153916715865636:ℤ)))) (.branch 197 (.branch 193 (.leaf (3203113641659761:ℤ)) (.leaf (3278979577611558:ℤ))) (.branch 200 (.leaf (3384175553962630:ℤ)) (.leaf (3466259114462912:ℤ))))))), (.branch 166 (.branch 146 (.branch 134 (.branch 122 (.leaf (1872944346873873:ℤ)) (.branch 130 (.leaf (1997054974742437:ℤ)) (.leaf (2104797716846394:ℤ)))) (.branch 138 (.leaf (2161747071203702:ℤ)) (.branch 142 (.leaf (2220887464731964:ℤ)) (.leaf (2282331581668836:ℤ))))) (.branch 156 (.branch 150 (.leaf (2346199456763812:ℤ)) (.branch 153 (.leaf (2412619060416094:ℤ)) (.leaf (2464190134410782:ℤ)))) (.branch 162 (.branch 160 (.leaf (2517334168676006:ℤ)) (.leaf (2590750988239955:ℤ))) (.branch 164 (.leaf (2628600866382160:ℤ)) (.leaf (2667239744196214:ℤ)))))) (.branch 182 (.branch 173 (.branch 168 (.leaf (2706689552648969:ℤ)) (.branch 170 (.leaf (2746972992171980:ℤ)) (.leaf (2788113565420612:ℤ)))) (.branch 178 (.branch 176 (.leaf (2851485030834598:ℤ)) (.leaf (2916925882203229:ℤ))) (.branch 180 (.leaf (2961747302796569:ℤ)) (.leaf (3007556670991113:ℤ))))) (.branch 190 (.branch 185 (.leaf (3054383089889191:ℤ)) (.branch 188 (.leaf (3126596029536933:ℤ)) (.leaf (3201272229395690:ℤ)))) (.branch 197 (.branch 193 (.leaf (3252480300746790:ℤ)) (.leaf (3331515920279105:ℤ))) (.branch 200 (.leaf (3441242106287443:ℤ)) (.leaf (3526967776954127:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 17 14) 8000 (endpointMeanRuns 17 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 17 14, EndpointRunConditions (endpointMeanCutoff 17 14) (endpointMeanBox 17 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 17 14 h) (endpointMeanCornerA 17 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 14, endpointJoint24Q (endpointMeanCornerK 17 14 h) (endpointMeanCornerA 17 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 17 14, endpointRunWeightQ (endpointMeanCutoff 17 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 17 14) = (17604723/40000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 17 14 h = (logRoundedQ ((endpointMeanCutoff 17 14:ℚ)/200)).2+(17604723/40000000000000:ℚ)+((endpointMeanRuns 17 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 17 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 17 14) r*endpointJoint24Q (endpointMeanCornerK 17 14 h) (endpointMeanCornerA 17 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 17 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 17 14 h≤endpointMeanCorner 17 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 17 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint17_14

namespace EndpointAnalyticJoint17_15
private noncomputable def weights : IntegerLookupTree := (.branch 1527 (.branch 1192 (.branch 1051 (.branch 1008 (.branch 977 (.leaf (89175288000000:ℤ)) (.leaf (1962758000000:ℤ))) (.branch 1029 (.leaf (1249495800000:ℤ)) (.leaf (1256914500000:ℤ)))) (.branch 1111 (.branch 1086 (.leaf (1918624900000:ℤ)) (.leaf (1274900900000:ℤ))) (.branch 1150 (.leaf (1893665200000:ℤ)) (.leaf (1882428700000:ℤ))))) (.branch 1339 (.branch 1253 (.branch 1222 (.leaf (1231692300000:ℤ)) (.leaf (1196105000000:ℤ))) (.branch 1286 (.leaf (1192555500000:ℤ)) (.leaf (1781260300000:ℤ)))) (.branch 1437 (.branch 1396 (.leaf (1708744800000:ℤ)) (.leaf (1089124700000:ℤ))) (.branch 1481 (.leaf (1067172400000:ℤ)) (.leaf (1012700600000:ℤ)))))) (.branch 2124 (.branch 1745 (.branch 1629 (.branch 1576 (.leaf (973861200000:ℤ)) (.leaf (942591500000:ℤ))) (.branch 1685 (.leaf (883672000000:ℤ)) (.leaf (833419900000:ℤ)))) (.branch 1954 (.branch 1844 (.leaf (1181096000000:ℤ)) (.leaf (1040989100000:ℤ))) (.branch 2036 (.leaf (609179700000:ℤ)) (.leaf (539194100000:ℤ))))) (.branch 2571 (.branch 2326 (.branch 2221 (.leaf (481550500000:ℤ)) (.leaf (413765000000:ℤ))) (.branch 2443 (.leaf (357323400000:ℤ)) (.leaf (294593800000:ℤ)))) (.branch 3257 (.branch 2874 (.leaf (463492100000:ℤ)) (.leaf (268783000000:ℤ))) (.branch 3758 (.leaf (129016900000:ℤ)) (.branch 4441 (.leaf (46399400000:ℤ)) (.leaf (23136700000:ℤ))))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 144 (.branch 134 (.branch 126 (.branch 122 (.leaf (1868268935145002:ℤ)) (.leaf (1990824690199289:ℤ))) (.branch 130 (.leaf (2042967079031380:ℤ)) (.leaf (2097020396067396:ℤ)))) (.branch 140 (.branch 138 (.leaf (2153077040683481:ℤ)) (.leaf (2211235026097485:ℤ))) (.branch 142 (.leaf (2241134286780632:ℤ)) (.leaf (2271598392760492:ℤ))))) (.branch 153 (.branch 148 (.branch 146 (.leaf (2302641364554991:ℤ)) (.leaf (2334277657681596:ℤ))) (.branch 150 (.leaf (2366522178922096:ℤ)) (.leaf (2399390303300863:ℤ)))) (.branch 158 (.branch 156 (.leaf (2449896579102040:ℤ)) (.leaf (2501897446990475:ℤ))) (.branch 160 (.leaf (2537423736321495:ℤ)) (.leaf (2573658176460049:ℤ)))))) (.branch 180 (.branch 170 (.branch 166 (.branch 164 (.leaf (2610619353200399:ℤ)) (.leaf (2648326462709837:ℤ))) (.branch 168 (.leaf (2686799335702825:ℤ)) (.leaf (2726058462739149:ℤ)))) (.branch 176 (.branch 173 (.leaf (2766125020706335:ℤ)) (.leaf (2827786879466387:ℤ))) (.branch 178 (.leaf (2891391935604934:ℤ)) (.leaf (2934914711427295:ℤ))))) (.branch 190 (.branch 185 (.branch 182 (.leaf (2979362115688595:ℤ)) (.leaf (3024760074241322:ℤ))) (.branch 188 (.leaf (3094698264925305:ℤ)) (.leaf (3166930429001032:ℤ)))) (.branch 195 (.branch 193 (.leaf (3216408669081256:ℤ)) (.leaf (3292688449385779:ℤ))) (.branch 197 (.leaf (3344963689012863:ℤ)) (.branch 200 (.leaf (3398415816277163:ℤ)) (.leaf (3480877682232817:ℤ)))))))), (.branch 162 (.branch 144 (.branch 134 (.branch 126 (.branch 122 (.leaf (1876383872041191:ℤ)) (.leaf (2001277182665232:ℤ))) (.branch 130 (.leaf (2054495012590715:ℤ)) (.leaf (2109713121195399:ℤ)))) (.branch 140 (.branch 138 (.leaf (2167030652099612:ℤ)) (.leaf (2226552906684004:ℤ))) (.branch 142 (.leaf (2257175508753568:ℤ)) (.leaf (2288391806409077:ℤ))))) (.branch 153 (.branch 148 (.branch 146 (.leaf (2320216906764472:ℤ)) (.leaf (2352666396017378:ℤ))) (.branch 150 (.leaf (2385756357708420:ℤ)) (.leaf (2419503391795183:ℤ)))) (.branch 158 (.branch 156 (.leaf (2471393591099463:ℤ)) (.leaf (2524861099152819:ℤ))) (.branch 160 (.leaf (2561413467549861:ℤ)) (.leaf (2598714384476894:ℤ)))))) (.branch 180 (.branch 170 (.branch 166 (.branch 164 (.leaf (2636784000151380:ℤ)) (.leaf (2675643141370335:ℤ))) (.branch 168 (.leaf (2715313338829304:ℤ)) (.leaf (2755816855733348:ℤ)))) (.branch 176 (.branch 173 (.leaf (2797176717770448:ℤ)) (.leaf (2860874488434693:ℤ))) (.branch 178 (.leaf (2926636739112141:ℤ)) (.leaf (2971668620002820:ℤ))))) (.branch 190 (.branch 185 (.branch 182 (.leaf (3017684565925307:ℤ)) (.leaf (3064712893190992:ℤ))) (.branch 188 (.leaf (3137218055386044:ℤ)) (.leaf (3212170852140127:ℤ)))) (.branch 195 (.branch 193 (.leaf (3263552887623513:ℤ)) (.leaf (3342830873369816:ℤ))) (.branch 197 (.leaf (3397204522274860:ℤ)) (.branch 200 (.leaf (3452838612922076:ℤ)) (.leaf (3538737767918817:ℤ)))))))), (.branch 162 (.branch 144 (.branch 134 (.branch 126 (.branch 122 (.leaf (1872944346873873:ℤ)) (.leaf (1997054974742437:ℤ))) (.branch 130 (.leaf (2049933532671927:ℤ)) (.leaf (2104797716846394:ℤ)))) (.branch 140 (.branch 138 (.leaf (2161747071203702:ℤ)) (.leaf (2220887464731964:ℤ))) (.branch 142 (.leaf (2251314234481133:ℤ)) (.leaf (2282331581668836:ℤ))))) (.branch 153 (.branch 148 (.branch 146 (.leaf (2313954744509290:ℤ)) (.leaf (2346199456763812:ℤ))) (.branch 150 (.leaf (2379081967276253:ℤ)) (.leaf (2412619060416094:ℤ)))) (.branch 158 (.branch 156 (.leaf (2464190134410782:ℤ)) (.leaf (2517334168676006:ℤ))) (.branch 160 (.leaf (2553668917063685:ℤ)) (.leaf (2590750988239955:ℤ)))))) (.branch 180 (.branch 170 (.branch 166 (.branch 164 (.leaf (2628600866382160:ℤ)) (.leaf (2667239744196214:ℤ))) (.branch 168 (.leaf (2706689552648969:ℤ)) (.leaf (2746972992171980:ℤ)))) (.branch 176 (.branch 173 (.leaf (2788113565420612:ℤ)) (.leaf (2851485030834598:ℤ))) (.branch 178 (.leaf (2916925882203229:ℤ)) (.leaf (2961747302796569:ℤ))))) (.branch 190 (.branch 185 (.branch 182 (.leaf (3007556670991113:ℤ)) (.leaf (3054383089889191:ℤ))) (.branch 188 (.leaf (3126596029536933:ℤ)) (.leaf (3201272229395690:ℤ)))) (.branch 195 (.branch 193 (.leaf (3252480300746790:ℤ)) (.leaf (3331515920279105:ℤ))) (.branch 197 (.leaf (3385742262044064:ℤ)) (.branch 200 (.leaf (3441242106287443:ℤ)) (.leaf (3526967776954127:ℤ)))))))), (.branch 162 (.branch 144 (.branch 134 (.branch 126 (.branch 122 (.leaf (1881393057171191:ℤ)) (.leaf (2007958407530205:ℤ))) (.branch 130 (.leaf (2061968675527620:ℤ)) (.leaf (2118060173011629:ℤ)))) (.branch 140 (.branch 138 (.leaf (2176339866906059:ℤ)) (.leaf (2236921670672266:ℤ))) (.branch 142 (.leaf (2268113495153397:ℤ)) (.leaf (2299926992977306:ℤ))))) (.branch 153 (.branch 148 (.branch 146 (.leaf (2332378609766159:ℤ)) (.leaf (2365485337647525:ℤ))) (.branch 150 (.leaf (2399264737205180:ℤ)) (.leaf (2433734960466557:ℤ)))) (.branch 158 (.branch 156 (.leaf (2486776818314746:ℤ)) (.leaf (2541481478227089:ℤ))) (.branch 160 (.leaf (2578909212929420:ℤ)) (.leaf (2617128287661435:ℤ)))))) (.branch 180 (.branch 170 (.branch 166 (.branch 164 (.leaf (2656160951466830:ℤ)) (.leaf (2696030239978838:ℤ))) (.branch 168 (.leaf (2736760009056104:ℤ)) (.leaf (2778374970110655:ℤ)))) (.branch 176 (.branch 173 (.leaf (2820900727226087:ℤ)) (.leaf (2886455417315588:ℤ))) (.branch 178 (.leaf (2954213039285470:ℤ)) (.leaf (3000657283343439:ℤ))))) (.branch 190 (.branch 185 (.branch 182 (.leaf (3048155172187571:ℤ)) (.leaf (3096738559762162:ℤ))) (.branch 188 (.leaf (3171721628953824:ℤ)) (.leaf (3249338777763926:ℤ)))) (.branch 195 (.branch 193 (.leaf (3302607802970237:ℤ)) (.leaf (3384894008750663:ℤ))) (.branch 197 (.leaf (3441398878927003:ℤ)) (.branch 200 (.leaf (3499270958393204:ℤ)) (.leaf (3588739701475022:ℤ))))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 17 15) 8000 (endpointMeanRuns 17 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 17 15, EndpointRunConditions (endpointMeanCutoff 17 15) (endpointMeanBox 17 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 17 15 h) (endpointMeanCornerA 17 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 15, endpointJoint24Q (endpointMeanCornerK 17 15 h) (endpointMeanCornerA 17 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 17 15, endpointRunWeightQ (endpointMeanCutoff 17 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 17 15) = (219373811/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 17 15 h = (logRoundedQ ((endpointMeanCutoff 17 15:ℚ)/200)).2+(219373811/500000000000000:ℚ)+((endpointMeanRuns 17 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 17 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 17 15) r*endpointJoint24Q (endpointMeanCornerK 17 15 h) (endpointMeanCornerA 17 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 17 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 17 15 h≤endpointMeanCorner 17 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 17 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint17_15

namespace EndpointAnalyticJoint17_16
private noncomputable def weights : IntegerLookupTree := (.branch 1527 (.branch 1192 (.branch 1051 (.branch 1008 (.branch 977 (.leaf (86002275900000:ℤ)) (.leaf (1948934400000:ℤ))) (.branch 1029 (.leaf (1240831600000:ℤ)) (.leaf (1248304800000:ℤ)))) (.branch 1111 (.branch 1086 (.leaf (1905683600000:ℤ)) (.leaf (1266437500000:ℤ))) (.branch 1150 (.leaf (1881292000000:ℤ)) (.leaf (1870364500000:ℤ))))) (.branch 1339 (.branch 1253 (.branch 1222 (.leaf (1223928200000:ℤ)) (.leaf (1188664800000:ℤ))) (.branch 1286 (.leaf (1185236000000:ℤ)) (.leaf (1770511500000:ℤ)))) (.branch 1437 (.branch 1396 (.leaf (1698645900000:ℤ)) (.leaf (1082801200000:ℤ))) (.branch 1481 (.leaf (1061065400000:ℤ)) (.leaf (1006989700000:ℤ)))))) (.branch 2124 (.branch 1745 (.branch 1629 (.branch 1576 (.leaf (968449900000:ℤ)) (.leaf (937432700000:ℤ))) (.branch 1685 (.leaf (878909600000:ℤ)) (.leaf (828998000000:ℤ)))) (.branch 1954 (.branch 1844 (.leaf (1174951900000:ℤ)) (.leaf (1035705500000:ℤ))) (.branch 2036 (.leaf (606153500000:ℤ)) (.leaf (536561800000:ℤ))))) (.branch 2571 (.branch 2326 (.branch 2221 (.leaf (479241200000:ℤ)) (.leaf (411816800000:ℤ))) (.branch 2443 (.leaf (355672300000:ℤ)) (.leaf (293258700000:ℤ)))) (.branch 3257 (.branch 2874 (.leaf (461450300000:ℤ)) (.leaf (267647900000:ℤ))) (.branch 3758 (.leaf (128496200000:ℤ)) (.branch 4441 (.leaf (46221100000:ℤ)) (.leaf (23052800000:ℤ))))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 144 (.branch 134 (.branch 126 (.branch 122 (.leaf (1876383872041191:ℤ)) (.leaf (2001277182665232:ℤ))) (.branch 130 (.leaf (2054495012590715:ℤ)) (.leaf (2109713121195399:ℤ)))) (.branch 140 (.branch 138 (.leaf (2167030652099612:ℤ)) (.leaf (2226552906684004:ℤ))) (.branch 142 (.leaf (2257175508753568:ℤ)) (.leaf (2288391806409077:ℤ))))) (.branch 153 (.branch 148 (.branch 146 (.leaf (2320216906764472:ℤ)) (.leaf (2352666396017378:ℤ))) (.branch 150 (.leaf (2385756357708420:ℤ)) (.leaf (2419503391795183:ℤ)))) (.branch 158 (.branch 156 (.leaf (2471393591099463:ℤ)) (.leaf (2524861099152819:ℤ))) (.branch 160 (.leaf (2561413467549861:ℤ)) (.leaf (2598714384476894:ℤ)))))) (.branch 180 (.branch 170 (.branch 166 (.branch 164 (.leaf (2636784000151380:ℤ)) (.leaf (2675643141370335:ℤ))) (.branch 168 (.leaf (2715313338829304:ℤ)) (.leaf (2755816855733348:ℤ)))) (.branch 176 (.branch 173 (.leaf (2797176717770448:ℤ)) (.leaf (2860874488434693:ℤ))) (.branch 178 (.leaf (2926636739112141:ℤ)) (.leaf (2971668620002820:ℤ))))) (.branch 190 (.branch 185 (.branch 182 (.leaf (3017684565925307:ℤ)) (.leaf (3064712893190992:ℤ))) (.branch 188 (.leaf (3137218055386044:ℤ)) (.leaf (3212170852140127:ℤ)))) (.branch 195 (.branch 193 (.leaf (3263552887623513:ℤ)) (.leaf (3342830873369816:ℤ))) (.branch 197 (.leaf (3397204522274860:ℤ)) (.branch 200 (.leaf (3452838612922076:ℤ)) (.leaf (3538737767918817:ℤ)))))))), (.branch 162 (.branch 144 (.branch 134 (.branch 126 (.branch 122 (.leaf (1884534056646949:ℤ)) (.leaf (2011784554196763:ℤ))) (.branch 130 (.leaf (2066087995290349:ℤ)) (.leaf (2122482672124185:ℤ)))) (.branch 140 (.branch 138 (.leaf (2181074693754822:ℤ)) (.leaf (2241976898770611:ℤ))) (.branch 142 (.leaf (2273331547943793:ℤ)) (.leaf (2305309369970286:ℤ))))) (.branch 153 (.branch 148 (.branch 146 (.leaf (2337926599123740:ℤ)) (.leaf (2371199995311099:ℤ))) (.branch 150 (.leaf (2405146864475476:ℤ)) (.leaf (2439785079924262:ℤ)))) (.branch 158 (.branch 156 (.leaf (2493079232089945:ℤ)) (.leaf (2548035523072124:ℤ))) (.branch 160 (.leaf (2585630006463587:ℤ)) (.leaf (2624014530700421:ℤ)))))) (.branch 180 (.branch 170 (.branch 166 (.branch 164 (.leaf (2663210879414868:ℤ)) (.leaf (2703241583228671:ℤ))) (.branch 168 (.leaf (2744129950477188:ℤ)) (.leaf (2785900099410576:ℤ)))) (.branch 176 (.branch 173 (.leaf (2828576991953582:ℤ)) (.leaf (2894349251709142:ℤ))) (.branch 178 (.leaf (2962311161364209:ℤ)) (.leaf (3008882797420332:ℤ))))) (.branch 190 (.branch 185 (.branch 182 (.leaf (3056499943887863:ℤ)) (.leaf (3105193432588842:ℤ))) (.branch 188 (.leaf (3180322049031081:ℤ)) (.leaf (3258057546465685:ℤ)))) (.branch 195 (.branch 193 (.leaf (3311388118276061:ℤ)) (.leaf (3393736886962050:ℤ))) (.branch 197 (.leaf (3450261240226093:ℤ)) (.branch 200 (.leaf (3508132945292671:ℤ)) (.leaf (3597559619521690:ℤ)))))))), (.branch 162 (.branch 144 (.branch 134 (.branch 126 (.branch 122 (.leaf (1881393057171191:ℤ)) (.leaf (2007958407530205:ℤ))) (.branch 130 (.leaf (2061968675527620:ℤ)) (.leaf (2118060173011629:ℤ)))) (.branch 140 (.branch 138 (.leaf (2176339866906059:ℤ)) (.leaf (2236921670672266:ℤ))) (.branch 142 (.leaf (2268113495153397:ℤ)) (.leaf (2299926992977306:ℤ))))) (.branch 153 (.branch 148 (.branch 146 (.leaf (2332378609766159:ℤ)) (.leaf (2365485337647525:ℤ))) (.branch 150 (.leaf (2399264737205180:ℤ)) (.leaf (2433734960466557:ℤ)))) (.branch 158 (.branch 156 (.leaf (2486776818314746:ℤ)) (.leaf (2541481478227089:ℤ))) (.branch 160 (.leaf (2578909212929420:ℤ)) (.leaf (2617128287661435:ℤ)))))) (.branch 180 (.branch 170 (.branch 166 (.branch 164 (.leaf (2656160951466830:ℤ)) (.leaf (2696030239978838:ℤ))) (.branch 168 (.leaf (2736760009056104:ℤ)) (.leaf (2778374970110655:ℤ)))) (.branch 176 (.branch 173 (.leaf (2820900727226087:ℤ)) (.leaf (2886455417315588:ℤ))) (.branch 178 (.leaf (2954213039285470:ℤ)) (.leaf (3000657283343439:ℤ))))) (.branch 190 (.branch 185 (.branch 182 (.leaf (3048155172187571:ℤ)) (.leaf (3096738559762162:ℤ))) (.branch 188 (.leaf (3171721628953824:ℤ)) (.leaf (3249338777763926:ℤ)))) (.branch 195 (.branch 193 (.leaf (3302607802970237:ℤ)) (.leaf (3384894008750663:ℤ))) (.branch 197 (.leaf (3441398878927003:ℤ)) (.branch 200 (.leaf (3499270958393204:ℤ)) (.leaf (3588739701475022:ℤ)))))))), (.branch 162 (.branch 144 (.branch 134 (.branch 126 (.branch 122 (.leaf (1889879878961678:ℤ)) (.leaf (2018921370400046:ℤ))) (.branch 130 (.leaf (2074074476607709:ℤ)) (.leaf (2131406196705526:ℤ)))) (.branch 140 (.branch 138 (.leaf (2191031170749932:ℤ)) (.leaf (2253071639236390:ℤ))) (.branch 142 (.leaf (2285038111564467:ℤ)) (.leaf (2317658054382196:ℤ))))) (.branch 153 (.branch 148 (.branch 146 (.leaf (2350949167092873:ℤ)) (.leaf (2384929749469599:ℤ))) (.branch 150 (.leaf (2419618726204155:ℤ)) (.leaf (2455035672633549:ℤ)))) (.branch 158 (.branch 156 (.leaf (2509570531003809:ℤ)) (.leaf (2565860418749462:ℤ))) (.branch 160 (.leaf (2604398982221846:ℤ)) (.leaf (2643774143161036:ℤ)))))) (.branch 180 (.branch 170 (.branch 166 (.branch 164 (.leaf (2684009995708281:ℤ)) (.leaf (2725131503718938:ℤ))) (.branch 168 (.leaf (2767164538629347:ℤ)) (.leaf (2810135919259196:ℤ)))) (.branch 176 (.branch 173 (.leaf (2854073453662996:ℤ)) (.leaf (2921854677845502:ℤ))) (.branch 178 (.leaf (2991976839292293:ℤ)) (.leaf (3040078444092863:ℤ))))) (.branch 190 (.branch 185 (.branch 182 (.leaf (3089301705717149:ℤ)) (.leaf (3139681377644654:ℤ))) (.branch 188 (.leaf (3217498518049163:ℤ)) (.leaf (3298127037035348:ℤ)))) (.branch 195 (.branch 193 (.leaf (3353507874509038:ℤ)) (.leaf (3439127329614034:ℤ))) (.branch 197 (.leaf (3497970408630560:ℤ)) (.branch 200 (.leaf (3558278337313609:ℤ)) (.leaf (3651593510180961:ℤ))))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 17 16) 8000 (endpointMeanRuns 17 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 17 16, EndpointRunConditions (endpointMeanCutoff 17 16) (endpointMeanBox 17 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 17 16 h) (endpointMeanCornerA 17 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 16, endpointJoint24Q (endpointMeanCornerK 17 16 h) (endpointMeanCornerA 17 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 17 16, endpointRunWeightQ (endpointMeanCutoff 17 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 17 16) = (218696647/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 17 16 h = (logRoundedQ ((endpointMeanCutoff 17 16:ℚ)/200)).2+(218696647/500000000000000:ℚ)+((endpointMeanRuns 17 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 17 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 17 16) r*endpointJoint24Q (endpointMeanCornerK 17 16 h) (endpointMeanCornerA 17 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 17 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 17 16 h≤endpointMeanCorner 17 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 17 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint17_16

namespace EndpointAnalyticJoint17_17
private noncomputable def weights : IntegerLookupTree := (.branch 1481 (.branch 1150 (.branch 1051 (.branch 977 (.leaf (82935072300000:ℤ)) (.branch 1008 (.leaf (1935271600000:ℤ)) (.leaf (2536185200000:ℤ)))) (.branch 1086 (.leaf (1892892700000:ℤ)) (.branch 1111 (.leaf (1258072500000:ℤ)) (.leaf (1869062700000:ℤ))))) (.branch 1286 (.branch 1192 (.leaf (1858440600000:ℤ)) (.branch 1222 (.leaf (1216254400000:ℤ)) (.leaf (2434564000000:ℤ)))) (.branch 1339 (.leaf (1759887700000:ℤ)) (.branch 1396 (.leaf (1688664400000:ℤ)) (.leaf (2210473000000:ℤ)))))) (.branch 2124 (.branch 1745 (.branch 1527 (.leaf (1001345200000:ℤ)) (.branch 1629 (.leaf (1973014500000:ℤ)) (.leaf (1774239100000:ℤ)))) (.branch 1844 (.leaf (1168879100000:ℤ)) (.branch 1954 (.leaf (1030483300000:ℤ)) (.leaf (1200290100000:ℤ))))) (.branch 2874 (.branch 2326 (.leaf (941478500000:ℤ)) (.branch 2571 (.leaf (690710900000:ℤ)) (.leaf (459432200000:ℤ)))) (.branch 3257 (.leaf (266526000000:ℤ)) (.branch 4441 (.leaf (226654800000:ℤ)) (.leaf (22969900000:ℤ)))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.branch 134 (.branch 122 (.leaf (1884534056646949:ℤ)) (.branch 130 (.leaf (2011784554196763:ℤ)) (.leaf (2122482672124185:ℤ)))) (.branch 138 (.leaf (2181074693754822:ℤ)) (.branch 142 (.leaf (2241976898770611:ℤ)) (.leaf (2305309369970286:ℤ))))) (.branch 156 (.branch 150 (.leaf (2371199995311099:ℤ)) (.branch 153 (.leaf (2439785079924262:ℤ)) (.leaf (2493079232089945:ℤ)))) (.branch 160 (.leaf (2548035523072124:ℤ)) (.branch 164 (.leaf (2624014530700421:ℤ)) (.leaf (2703241583228671:ℤ)))))) (.branch 185 (.branch 176 (.branch 170 (.leaf (2744129950477188:ℤ)) (.branch 173 (.leaf (2828576991953582:ℤ)) (.leaf (2894349251709142:ℤ)))) (.branch 180 (.leaf (2962311161364209:ℤ)) (.branch 182 (.leaf (3056499943887863:ℤ)) (.leaf (3105193432588842:ℤ))))) (.branch 193 (.branch 188 (.leaf (3180322049031081:ℤ)) (.branch 190 (.leaf (3258057546465685:ℤ)) (.leaf (3311388118276061:ℤ)))) (.branch 197 (.leaf (3393736886962050:ℤ)) (.branch 200 (.leaf (3508132945292671:ℤ)) (.leaf (3597559619521690:ℤ))))))), (.branch 166 (.branch 146 (.branch 134 (.branch 122 (.leaf (1892719642062801:ℤ)) (.branch 130 (.leaf (2022347092927252:ℤ)) (.leaf (2135329513860561:ℤ)))) (.branch 138 (.leaf (2195209751707301:ℤ)) (.branch 142 (.leaf (2257507737423125:ℤ)) (.leaf (2322352001256365:ℤ))))) (.branch 156 (.branch 150 (.leaf (2389879596733876:ℤ)) (.branch 153 (.leaf (2460236780988540:ℤ)) (.leaf (2514955157228959:ℤ)))) (.branch 160 (.leaf (2571422653315816:ℤ)) (.branch 164 (.leaf (2649560990025054:ℤ)) (.leaf (2731124694586172:ℤ)))))) (.branch 185 (.branch 176 (.branch 170 (.leaf (2773252382118292:ℤ)) (.branch 173 (.leaf (2860329756278834:ℤ)) (.leaf (2928215699337729:ℤ)))) (.branch 180 (.leaf (2998420439225796:ℤ)) (.branch 182 (.leaf (3095814589926141:ℤ)) (.leaf (3146208662878484:ℤ))))) (.branch 193 (.branch 188 (.leaf (3224018272554742:ℤ)) (.branch 190 (.leaf (3304599744129343:ℤ)) (.leaf (3359924489486263:ℤ)))) (.branch 197 (.leaf (3445418118421422:ℤ)) (.branch 200 (.leaf (3564312770307172:ℤ)) (.leaf (3657359223773372:ℤ))))))), (.branch 166 (.branch 146 (.branch 134 (.branch 122 (.leaf (1889879878961678:ℤ)) (.branch 130 (.leaf (2018921370400046:ℤ)) (.leaf (2131406196705526:ℤ)))) (.branch 138 (.leaf (2191031170749932:ℤ)) (.branch 142 (.leaf (2253071639236390:ℤ)) (.leaf (2317658054382196:ℤ))))) (.branch 156 (.branch 150 (.leaf (2384929749469599:ℤ)) (.branch 153 (.leaf (2455035672633549:ℤ)) (.leaf (2509570531003809:ℤ)))) (.branch 160 (.leaf (2565860418749462:ℤ)) (.branch 164 (.leaf (2643774143161036:ℤ)) (.leaf (2725131503718938:ℤ)))))) (.branch 185 (.branch 176 (.branch 170 (.leaf (2767164538629347:ℤ)) (.branch 173 (.leaf (2854073453662996:ℤ)) (.leaf (2921854677845502:ℤ)))) (.branch 180 (.leaf (2991976839292293:ℤ)) (.branch 182 (.leaf (3089301705717149:ℤ)) (.leaf (3139681377644654:ℤ))))) (.branch 193 (.branch 188 (.leaf (3217498518049163:ℤ)) (.branch 190 (.leaf (3298127037035348:ℤ)) (.leaf (3353507874509038:ℤ)))) (.branch 197 (.leaf (3439127329614034:ℤ)) (.branch 200 (.leaf (3558278337313609:ℤ)) (.leaf (3651593510180961:ℤ))))))), (.branch 166 (.branch 146 (.branch 134 (.branch 122 (.leaf (1898404984163401:ℤ)) (.branch 130 (.leaf (2029944188371685:ℤ)) (.leaf (2144836314492079:ℤ)))) (.branch 138 (.leaf (2205821647710980:ℤ)) (.branch 142 (.leaf (2269338206199129:ℤ)) (.leaf (2335525811664610:ℤ))))) (.branch 156 (.branch 150 (.leaf (2404533995362546:ℤ)) (.branch 153 (.leaf (2476522814443128:ℤ)) (.leaf (2532573170096852:ℤ)))) (.branch 160 (.leaf (2590473212143111:ℤ)) (.branch 164 (.leaf (2670691288997701:ℤ)) (.leaf (2754546889881967:ℤ)))))) (.branch 185 (.branch 176 (.branch 170 (.leaf (2797906852814876:ℤ)) (.branch 173 (.leaf (2887636278825692:ℤ)) (.leaf (2957688072101703:ℤ)))) (.branch 180 (.leaf (3030223375165485:ℤ)) (.branch 182 (.leaf (3131003669376054:ℤ)) (.leaf (3183219688356808:ℤ))))) (.branch 193 (.branch 188 (.leaf (3263936096770017:ℤ)) (.branch 190 (.leaf (3347647843574240:ℤ)) (.leaf (3405192422267003:ℤ)))) (.branch 197 (.leaf (3494229585541333:ℤ)) (.branch 200 (.leaf (3618280743715012:ℤ)) (.leaf (3715548151378932:ℤ)))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 17 17) 8000 (endpointMeanRuns 17 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 17 17, EndpointRunConditions (endpointMeanCutoff 17 17) (endpointMeanBox 17 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 17 17 h) (endpointMeanCornerA 17 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 17, endpointJoint24Q (endpointMeanCornerK 17 17 h) (endpointMeanCornerA 17 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 17 17, endpointRunWeightQ (endpointMeanCutoff 17 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 17 17) = (218027357/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 17 17 h = (logRoundedQ ((endpointMeanCutoff 17 17:ℚ)/200)).2+(218027357/500000000000000:ℚ)+((endpointMeanRuns 17 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 17 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 17 17) r*endpointJoint24Q (endpointMeanCornerK 17 17 h) (endpointMeanCornerA 17 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 17 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 17 17 h≤endpointMeanCorner 17 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 17 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint17_17

namespace EndpointAnalyticJoint17_18
private noncomputable def weights : IntegerLookupTree := (.branch 1481 (.branch 1150 (.branch 1051 (.branch 977 (.leaf (79970000100000:ℤ)) (.leaf (4640662100000:ℤ))) (.branch 1111 (.leaf (3232954100000:ℤ)) (.leaf (1856973900000:ℤ)))) (.branch 1286 (.branch 1222 (.leaf (3166427400000:ℤ)) (.leaf (2419680100000:ℤ))) (.branch 1396 (.leaf (3608825300000:ℤ)) (.leaf (2197875500000:ℤ))))) (.branch 2124 (.branch 1745 (.branch 1629 (.leaf (3119424700000:ℤ)) (.leaf (1764864500000:ℤ))) (.branch 1954 (.leaf (2355333400000:ℤ)) (.leaf (1194452100000:ℤ)))) (.branch 3257 (.branch 2571 (.leaf (1856732700000:ℤ)) (.leaf (864497000000:ℤ))) (.branch 4441 (.leaf (225762800000:ℤ)) (.leaf (22888000000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 146 (.branch 130 (.branch 122 (.leaf (1892719642062801:ℤ)) (.leaf (2022347092927252:ℤ))) (.branch 138 (.leaf (2135329513860561:ℤ)) (.leaf (2257507737423125:ℤ)))) (.branch 156 (.branch 150 (.leaf (2389879596733876:ℤ)) (.leaf (2460236780988540:ℤ))) (.branch 160 (.leaf (2571422653315816:ℤ)) (.leaf (2649560990025054:ℤ))))) (.branch 185 (.branch 176 (.branch 170 (.leaf (2773252382118292:ℤ)) (.leaf (2860329756278834:ℤ))) (.branch 180 (.leaf (2998420439225796:ℤ)) (.leaf (3095814589926141:ℤ)))) (.branch 193 (.branch 188 (.leaf (3224018272554742:ℤ)) (.leaf (3304599744129343:ℤ))) (.branch 200 (.leaf (3445418118421422:ℤ)) (.leaf (3657359223773372:ℤ)))))), (.branch 166 (.branch 146 (.branch 130 (.branch 122 (.leaf (1900940782054256:ℤ)) (.leaf (2032965088502858:ℤ))) (.branch 138 (.leaf (2148254114225907:ℤ)) (.leaf (2273146162799382:ℤ)))) (.branch 156 (.branch 150 (.leaf (2408706350446632:ℤ)) (.leaf (2480859920135568:ℤ))) (.branch 160 (.leaf (2595024442207742:ℤ)) (.leaf (2675356160466337:ℤ))))) (.branch 185 (.branch 176 (.branch 170 (.leaf (2802683879306583:ℤ)) (.leaf (2892438967695735:ℤ))) (.branch 180 (.leaf (3034969873396645:ℤ)) (.leaf (3135634925943639:ℤ)))) (.branch 193 (.branch 188 (.leaf (3268314862934591:ℤ)) (.leaf (3351806809166419:ℤ))) (.branch 200 (.leaf (3497886373086814:ℤ)) (.leaf (3718152833141528:ℤ)))))), (.branch 166 (.branch 146 (.branch 130 (.branch 122 (.leaf (1898404984163401:ℤ)) (.leaf (2029944188371685:ℤ))) (.branch 138 (.leaf (2144836314492079:ℤ)) (.leaf (2269338206199129:ℤ)))) (.branch 156 (.branch 150 (.leaf (2404533995362546:ℤ)) (.leaf (2476522814443128:ℤ))) (.branch 160 (.leaf (2590473212143111:ℤ)) (.leaf (2670691288997701:ℤ))))) (.branch 185 (.branch 176 (.branch 170 (.leaf (2797906852814876:ℤ)) (.leaf (2887636278825692:ℤ))) (.branch 180 (.leaf (3030223375165485:ℤ)) (.leaf (3131003669376054:ℤ)))) (.branch 193 (.branch 188 (.leaf (3263936096770017:ℤ)) (.leaf (3347647843574240:ℤ))) (.branch 200 (.leaf (3494229585541333:ℤ)) (.leaf (3715548151378932:ℤ)))))), (.branch 166 (.branch 146 (.branch 130 (.branch 122 (.leaf (1906968545469937:ℤ)) (.leaf (2041027188239367:ℤ))) (.branch 138 (.leaf (2158351056253187:ℤ)) (.leaf (2285722213369339:ℤ)))) (.branch 156 (.branch 150 (.leaf (2424299389170695:ℤ)) (.leaf (2498198017578369:ℤ))) (.branch 160 (.leaf (2615322101621417:ℤ)) (.leaf (2697882487268779:ℤ))))) (.branch 185 (.branch 176 (.branch 170 (.leaf (2828990704291837:ℤ)) (.leaf (2921593790127758:ℤ))) (.branch 180 (.leaf (3068958817733104:ℤ)) (.leaf (3173268560822105:ℤ)))) (.branch 193 (.branch 188 (.leaf (3311043900731176:ℤ)) (.leaf (3397912196451020:ℤ))) (.branch 200 (.leaf (3550214698751095:ℤ)) (.leaf (3780622905239869:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 17 18) 8000 (endpointMeanRuns 17 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 17 18, EndpointRunConditions (endpointMeanCutoff 17 18) (endpointMeanBox 17 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 17 18 h) (endpointMeanCornerA 17 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 18, endpointJoint24Q (endpointMeanCornerK 17 18 h) (endpointMeanCornerA 17 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 17 18, endpointRunWeightQ (endpointMeanCutoff 17 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 17 18) = (169817/390625000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 17 18 h = (logRoundedQ ((endpointMeanCutoff 17 18:ℚ)/200)).2+(169817/390625000000:ℚ)+((endpointMeanRuns 17 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 17 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 17 18) r*endpointJoint24Q (endpointMeanCornerK 17 18 h) (endpointMeanCornerA 17 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 17 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 17 18 h≤endpointMeanCorner 17 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 17 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint17_18

namespace EndpointAnalyticJoint17_19
private noncomputable def weights : IntegerLookupTree := (.branch 1481 (.branch 1051 (.branch 977 (.leaf (77103521400000:ℤ)) (.leaf (4608796900000:ℤ))) (.branch 1150 (.leaf (5327131400000:ℤ)) (.branch 1286 (.leaf (5946710900000:ℤ)) (.leaf (6285866800000:ℤ))))) (.branch 2124 (.branch 1745 (.leaf (5377160200000:ℤ)) (.leaf (4004410600000:ℤ))) (.branch 2571 (.leaf (1848197500000:ℤ)) (.branch 3257 (.leaf (860818000000:ℤ)) (.leaf (571223500000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 138 (.branch 130 (.leaf (1900940782054256:ℤ)) (.leaf (2148254114225907:ℤ))) (.branch 146 (.leaf (2273146162799382:ℤ)) (.branch 156 (.leaf (2408706350446632:ℤ)) (.leaf (2595024442207742:ℤ))))) (.branch 185 (.branch 176 (.leaf (2802683879306583:ℤ)) (.leaf (3034969873396645:ℤ))) (.branch 193 (.leaf (3268314862934591:ℤ)) (.branch 200 (.leaf (3497886373086814:ℤ)) (.leaf (3718152833141528:ℤ)))))), (.branch 166 (.branch 138 (.branch 130 (.leaf (1909197631054727:ℤ)) (.leaf (2161256943873209:ℤ))) (.branch 146 (.leaf (2288892920184516:ℤ)) (.branch 156 (.leaf (2427681415670918:ℤ)) (.leaf (2618842859991145:ℤ))))) (.branch 185 (.branch 176 (.leaf (2832427722039880:ℤ)) (.leaf (3071964829189725:ℤ))) (.branch 193 (.leaf (3313220068946669:ℤ)) (.branch 200 (.leaf (3551153636073692:ℤ)) (.leaf (3779956970246747:ℤ)))))), (.branch 166 (.branch 138 (.branch 130 (.leaf (1906968545469937:ℤ)) (.leaf (2158351056253187:ℤ))) (.branch 146 (.leaf (2285722213369339:ℤ)) (.branch 156 (.leaf (2424299389170695:ℤ)) (.leaf (2615322101621417:ℤ))))) (.branch 185 (.branch 176 (.leaf (2828990704291837:ℤ)) (.leaf (3068958817733104:ℤ))) (.branch 193 (.leaf (3311043900731176:ℤ)) (.branch 200 (.leaf (3550214698751095:ℤ)) (.leaf (3780622905239869:ℤ)))))), (.branch 166 (.branch 138 (.branch 130 (.leaf (1915570736353858:ℤ)) (.leaf (2171950955209576:ℤ))) (.branch 146 (.leaf (2302224508633501:ℤ)) (.branch 156 (.leaf (2444227255538245:ℤ)) (.leaf (2640409351915584:ℤ))))) (.branch 185 (.branch 176 (.leaf (2860419887430455:ℤ)) (.leaf (3108189416705097:ℤ))) (.branch 193 (.leaf (3358831603173261:ℤ)) (.branch 200 (.leaf (3607096814525911:ℤ)) (.leaf (3846837389610961:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 17 19) 8000 (endpointMeanRuns 17 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 17 19, EndpointRunConditions (endpointMeanCutoff 17 19) (endpointMeanBox 17 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 17 19 h) (endpointMeanCornerA 17 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 17 19, endpointJoint24Q (endpointMeanCornerK 17 19 h) (endpointMeanCornerA 17 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 17 19, endpointRunWeightQ (endpointMeanCutoff 17 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 17 19) = (216711681/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 17 19 h = (logRoundedQ ((endpointMeanCutoff 17 19:ℚ)/200)).2+(216711681/500000000000000:ℚ)+((endpointMeanRuns 17 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 17 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 17 19) r*endpointJoint24Q (endpointMeanCornerK 17 19 h) (endpointMeanCornerA 17 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 17 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 17 19 h≤endpointMeanCorner 17 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 17 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint17_19

private theorem activeIndices12 : ∀ai : Fin 42, endpointMeanActive 12 ai → ai∈
    ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow12 (ai : Fin 42) : endpointMeanActive 12 ai →
    EndpointJointNumericalConditions 12 ai := by
  intro hact
  have hi := activeIndices12 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint12_02.conditions
  · exact EndpointAnalyticJoint12_03.conditions
  · exact EndpointAnalyticJoint12_04.conditions
  · exact EndpointAnalyticJoint12_05.conditions
  · exact EndpointAnalyticJoint12_06.conditions
  · exact EndpointAnalyticJoint12_07.conditions
  · exact EndpointAnalyticJoint12_08.conditions
  · exact EndpointAnalyticJoint12_09.conditions
  · exact EndpointAnalyticJoint12_10.conditions
  · exact EndpointAnalyticJoint12_11.conditions
  · exact EndpointAnalyticJoint12_12.conditions
  · exact EndpointAnalyticJoint12_13.conditions
  · exact EndpointAnalyticJoint12_14.conditions
  · exact EndpointAnalyticJoint12_15.conditions
  · exact EndpointAnalyticJoint12_16.conditions

private theorem activeIndices13 : ∀ai : Fin 42, endpointMeanActive 13 ai → ai∈
    ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow13 (ai : Fin 42) : endpointMeanActive 13 ai →
    EndpointJointNumericalConditions 13 ai := by
  intro hact
  have hi := activeIndices13 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint13_02.conditions
  · exact EndpointAnalyticJoint13_03.conditions
  · exact EndpointAnalyticJoint13_04.conditions
  · exact EndpointAnalyticJoint13_05.conditions
  · exact EndpointAnalyticJoint13_06.conditions
  · exact EndpointAnalyticJoint13_07.conditions
  · exact EndpointAnalyticJoint13_08.conditions
  · exact EndpointAnalyticJoint13_09.conditions
  · exact EndpointAnalyticJoint13_10.conditions
  · exact EndpointAnalyticJoint13_11.conditions
  · exact EndpointAnalyticJoint13_12.conditions
  · exact EndpointAnalyticJoint13_13.conditions
  · exact EndpointAnalyticJoint13_14.conditions
  · exact EndpointAnalyticJoint13_15.conditions
  · exact EndpointAnalyticJoint13_16.conditions
  · exact EndpointAnalyticJoint13_17.conditions

private theorem activeIndices14 : ∀ai : Fin 42, endpointMeanActive 14 ai → ai∈
    ([3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow14 (ai : Fin 42) : endpointMeanActive 14 ai →
    EndpointJointNumericalConditions 14 ai := by
  intro hact
  have hi := activeIndices14 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint14_03.conditions
  · exact EndpointAnalyticJoint14_04.conditions
  · exact EndpointAnalyticJoint14_05.conditions
  · exact EndpointAnalyticJoint14_06.conditions
  · exact EndpointAnalyticJoint14_07.conditions
  · exact EndpointAnalyticJoint14_08.conditions
  · exact EndpointAnalyticJoint14_09.conditions
  · exact EndpointAnalyticJoint14_10.conditions
  · exact EndpointAnalyticJoint14_11.conditions
  · exact EndpointAnalyticJoint14_12.conditions
  · exact EndpointAnalyticJoint14_13.conditions
  · exact EndpointAnalyticJoint14_14.conditions
  · exact EndpointAnalyticJoint14_15.conditions
  · exact EndpointAnalyticJoint14_16.conditions
  · exact EndpointAnalyticJoint14_17.conditions

private theorem activeIndices15 : ∀ai : Fin 42, endpointMeanActive 15 ai → ai∈
    ([3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow15 (ai : Fin 42) : endpointMeanActive 15 ai →
    EndpointJointNumericalConditions 15 ai := by
  intro hact
  have hi := activeIndices15 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint15_03.conditions
  · exact EndpointAnalyticJoint15_04.conditions
  · exact EndpointAnalyticJoint15_05.conditions
  · exact EndpointAnalyticJoint15_06.conditions
  · exact EndpointAnalyticJoint15_07.conditions
  · exact EndpointAnalyticJoint15_08.conditions
  · exact EndpointAnalyticJoint15_09.conditions
  · exact EndpointAnalyticJoint15_10.conditions
  · exact EndpointAnalyticJoint15_11.conditions
  · exact EndpointAnalyticJoint15_12.conditions
  · exact EndpointAnalyticJoint15_13.conditions
  · exact EndpointAnalyticJoint15_14.conditions
  · exact EndpointAnalyticJoint15_15.conditions
  · exact EndpointAnalyticJoint15_16.conditions
  · exact EndpointAnalyticJoint15_17.conditions
  · exact EndpointAnalyticJoint15_18.conditions

private theorem activeIndices16 : ∀ai : Fin 42, endpointMeanActive 16 ai → ai∈
    ([3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow16 (ai : Fin 42) : endpointMeanActive 16 ai →
    EndpointJointNumericalConditions 16 ai := by
  intro hact
  have hi := activeIndices16 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint16_03.conditions
  · exact EndpointAnalyticJoint16_04.conditions
  · exact EndpointAnalyticJoint16_05.conditions
  · exact EndpointAnalyticJoint16_06.conditions
  · exact EndpointAnalyticJoint16_07.conditions
  · exact EndpointAnalyticJoint16_08.conditions
  · exact EndpointAnalyticJoint16_09.conditions
  · exact EndpointAnalyticJoint16_10.conditions
  · exact EndpointAnalyticJoint16_11.conditions
  · exact EndpointAnalyticJoint16_12.conditions
  · exact EndpointAnalyticJoint16_13.conditions
  · exact EndpointAnalyticJoint16_14.conditions
  · exact EndpointAnalyticJoint16_15.conditions
  · exact EndpointAnalyticJoint16_16.conditions
  · exact EndpointAnalyticJoint16_17.conditions
  · exact EndpointAnalyticJoint16_18.conditions

private theorem activeIndices17 : ∀ai : Fin 42, endpointMeanActive 17 ai → ai∈
    ([3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow17 (ai : Fin 42) : endpointMeanActive 17 ai →
    EndpointJointNumericalConditions 17 ai := by
  intro hact
  have hi := activeIndices17 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint17_03.conditions
  · exact EndpointAnalyticJoint17_04.conditions
  · exact EndpointAnalyticJoint17_05.conditions
  · exact EndpointAnalyticJoint17_06.conditions
  · exact EndpointAnalyticJoint17_07.conditions
  · exact EndpointAnalyticJoint17_08.conditions
  · exact EndpointAnalyticJoint17_09.conditions
  · exact EndpointAnalyticJoint17_10.conditions
  · exact EndpointAnalyticJoint17_11.conditions
  · exact EndpointAnalyticJoint17_12.conditions
  · exact EndpointAnalyticJoint17_13.conditions
  · exact EndpointAnalyticJoint17_14.conditions
  · exact EndpointAnalyticJoint17_15.conditions
  · exact EndpointAnalyticJoint17_16.conditions
  · exact EndpointAnalyticJoint17_17.conditions
  · exact EndpointAnalyticJoint17_18.conditions
  · exact EndpointAnalyticJoint17_19.conditions

end SingularValueBounds.KL.Certificates
