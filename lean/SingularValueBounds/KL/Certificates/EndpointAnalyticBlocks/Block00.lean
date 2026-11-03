import SingularValueBounds.KL.Certificates.EndpointAnalyticLogs
import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SingularValueBounds.KL.Certificates

namespace EndpointAnalyticJoint00_00
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.leaf (170273469800000:ℤ)) (.branch 3048 (.leaf (3014020800000:ℤ)) (.leaf (466815000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 158 (.leaf (1843252922424056:ℤ)) (.branch 200 (.leaf (2209157663620759:ℤ)) (.leaf (2729901959585533:ℤ)))), (.branch 158 (.leaf (1844947912479987:ℤ)) (.branch 200 (.leaf (2212621634217641:ℤ)) (.leaf (2736897868126069:ℤ)))), (.branch 158 (.leaf (1843410719775582:ℤ)) (.branch 200 (.leaf (2209491065295543:ℤ)) (.leaf (2730602268728417:ℤ)))), (.branch 158 (.leaf (1845200626900267:ℤ)) (.branch 200 (.leaf (2213155937527381:ℤ)) (.leaf (2738021320692754:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 0 0) 8000 (endpointMeanRuns 0 0) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 0 0, EndpointRunConditions (endpointMeanCutoff 0 0) (endpointMeanBox 0 0).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 0, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 0 0 h) (endpointMeanCornerA 0 0 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 0, endpointJoint24Q (endpointMeanCornerK 0 0 h) (endpointMeanCornerA 0 0 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 0 0, endpointRunWeightQ (endpointMeanCutoff 0 0) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 0 0) = (462075431/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 0 0 h = (logRoundedQ ((endpointMeanCutoff 0 0:ℚ)/200)).2+(462075431/1000000000000000:ℚ)+((endpointMeanRuns 0 0).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 0 0).map (fun r => endpointRunWeightQ (endpointMeanCutoff 0 0) r*endpointJoint24Q (endpointMeanCornerK 0 0 h) (endpointMeanCornerA 0 0 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 0 0).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 0 0 h≤endpointMeanCorner 0 0 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 0 0 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint00_00

namespace EndpointAnalyticJoint00_01
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.leaf (167489095000000:ℤ)) (.branch 3048 (.leaf (3005569500000:ℤ)) (.leaf (465725700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 158 (.leaf (1844947912479987:ℤ)) (.branch 200 (.leaf (2212621634217641:ℤ)) (.leaf (2736897868126069:ℤ)))), (.branch 158 (.leaf (1849475509936183:ℤ)) (.branch 200 (.leaf (2221885466396434:ℤ)) (.leaf (2755641398963874:ℤ)))), (.branch 158 (.leaf (1845200626900267:ℤ)) (.branch 200 (.leaf (2213155937527381:ℤ)) (.leaf (2738021320692754:ℤ)))), (.branch 158 (.leaf (1849982213826087:ℤ)) (.branch 200 (.leaf (2222958676635214:ℤ)) (.leaf (2757904156250725:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 0 1) 8000 (endpointMeanRuns 0 1) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 0 1, EndpointRunConditions (endpointMeanCutoff 0 1) (endpointMeanBox 0 1).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 1, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 0 1 h) (endpointMeanCornerA 0 1 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 1, endpointJoint24Q (endpointMeanCornerK 0 1 h) (endpointMeanCornerA 0 1 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 0 1, endpointRunWeightQ (endpointMeanCutoff 0 1) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 0 1) = (461244261/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 0 1 h = (logRoundedQ ((endpointMeanCutoff 0 1:ℚ)/200)).2+(461244261/1000000000000000:ℚ)+((endpointMeanRuns 0 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 0 1).map (fun r => endpointRunWeightQ (endpointMeanCutoff 0 1) r*endpointJoint24Q (endpointMeanCornerK 0 1 h) (endpointMeanCornerA 0 1 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 0 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 0 1 h≤endpointMeanCorner 0 1 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 0 1 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint00_01

namespace EndpointAnalyticJoint00_02
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.leaf (163850991400000:ℤ)) (.branch 2490 (.leaf (1484452200000:ℤ)) (.leaf (2395269300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 171 (.leaf (1849475509936183:ℤ)) (.branch 200 (.leaf (2374640288345090:ℤ)) (.leaf (2755641398963874:ℤ)))), (.branch 171 (.leaf (1854014218350350:ℤ)) (.branch 200 (.leaf (2386359427957799:ℤ)) (.leaf (2774513294090453:ℤ)))), (.branch 171 (.leaf (1849982213826087:ℤ)) (.branch 200 (.leaf (2376008471892085:ℤ)) (.leaf (2757904156250725:ℤ)))), (.branch 171 (.leaf (1854776191585297:ℤ)) (.branch 200 (.leaf (2388422128549882:ℤ)) (.leaf (2777931376056858:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 0 2) 8000 (endpointMeanRuns 0 2) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 0 2, EndpointRunConditions (endpointMeanCutoff 0 2) (endpointMeanBox 0 2).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 2, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 0 2 h) (endpointMeanCornerA 0 2 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 2, endpointJoint24Q (endpointMeanCornerK 0 2 h) (endpointMeanCornerA 0 2 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 0 2, endpointRunWeightQ (endpointMeanCutoff 0 2) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 0 2) = (460145287/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 0 2 h = (logRoundedQ ((endpointMeanCutoff 0 2:ℚ)/200)).2+(460145287/1000000000000000:ℚ)+((endpointMeanRuns 0 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 0 2).map (fun r => endpointRunWeightQ (endpointMeanCutoff 0 2) r*endpointJoint24Q (endpointMeanCornerK 0 2 h) (endpointMeanCornerA 0 2 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 0 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 0 2 h≤endpointMeanCorner 0 2 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 0 2 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint00_02

namespace EndpointAnalyticJoint00_03
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.leaf (161177045400000:ℤ)) (.branch 2490 (.leaf (1480298800000:ℤ)) (.leaf (2389393900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 171 (.leaf (1854014218350350:ℤ)) (.branch 200 (.leaf (2386359427957799:ℤ)) (.leaf (2774513294090453:ℤ)))), (.branch 171 (.leaf (1858564064989365:ℤ)) (.branch 200 (.leaf (2398136402954645:ℤ)) (.leaf (2793514432603265:ℤ)))), (.branch 171 (.leaf (1854776191585297:ℤ)) (.branch 200 (.leaf (2388422128549882:ℤ)) (.leaf (2777931376056858:ℤ)))), (.branch 171 (.leaf (1859582592287050:ℤ)) (.branch 200 (.leaf (2400900641403870:ℤ)) (.leaf (2798104028593948:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 0 3) 8000 (endpointMeanRuns 0 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 0 3, EndpointRunConditions (endpointMeanCutoff 0 3) (endpointMeanBox 0 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 0 3 h) (endpointMeanCornerA 0 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 3, endpointJoint24Q (endpointMeanCornerK 0 3 h) (endpointMeanCornerA 0 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 0 3, endpointRunWeightQ (endpointMeanCutoff 0 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 0 3) = (28707993/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 0 3 h = (logRoundedQ ((endpointMeanCutoff 0 3:ℚ)/200)).2+(28707993/62500000000000:ℚ)+((endpointMeanRuns 0 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 0 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 0 3) r*endpointJoint24Q (endpointMeanCornerK 0 3 h) (endpointMeanCornerA 0 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 0 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 0 3 h≤endpointMeanCorner 0 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 0 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint00_03

namespace EndpointAnalyticJoint00_04
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.leaf (157682960700000:ℤ)) (.branch 3048 (.leaf (2975093000000:ℤ)) (.leaf (461797300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 158 (.leaf (1858564064989365:ℤ)) (.branch 200 (.leaf (2240529650931832:ℤ)) (.leaf (2793514432603265:ℤ)))), (.branch 158 (.leaf (1863125077186994:ℤ)) (.branch 200 (.leaf (2249910328747163:ℤ)) (.leaf (2812645699620256:ℤ)))), (.branch 158 (.leaf (1859582592287050:ℤ)) (.branch 200 (.leaf (2242694605084990:ℤ)) (.leaf (2798104028593948:ℤ)))), (.branch 158 (.leaf (1864401448123722:ℤ)) (.branch 200 (.leaf (2252628179913321:ℤ)) (.leaf (2818423169958618:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 0 4) 8000 (endpointMeanRuns 0 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 0 4, EndpointRunConditions (endpointMeanCutoff 0 4) (endpointMeanBox 0 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 0 4 h) (endpointMeanCornerA 0 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 4, endpointJoint24Q (endpointMeanCornerK 0 4 h) (endpointMeanCornerA 0 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 0 4, endpointRunWeightQ (endpointMeanCutoff 0 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 0 4) = (458246973/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 0 4 h = (logRoundedQ ((endpointMeanCutoff 0 4:ℚ)/200)).2+(458246973/1000000000000000:ℚ)+((endpointMeanRuns 0 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 0 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 0 4) r*endpointJoint24Q (endpointMeanCornerK 0 4 h) (endpointMeanCornerA 0 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 0 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 0 4 h≤endpointMeanCorner 0 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 0 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint00_04

namespace EndpointAnalyticJoint00_05
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.leaf (154268367700000:ℤ)) (.branch 3048 (.leaf (2964204500000:ℤ)) (.leaf (460393700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 158 (.leaf (1863125077186994:ℤ)) (.branch 200 (.leaf (2249910328747163:ℤ)) (.leaf (2812645699620256:ℤ)))), (.branch 158 (.leaf (1867697282344108:ℤ)) (.branch 200 (.leaf (2259330281702751:ℤ)) (.leaf (2831907986321059:ℤ)))), (.branch 158 (.leaf (1864401448123722:ℤ)) (.branch 200 (.leaf (2252628179913321:ℤ)) (.leaf (2818423169958618:ℤ)))), (.branch 158 (.leaf (1869232791371098:ℤ)) (.branch 200 (.leaf (2262605753558365:ℤ)) (.leaf (2838889863916612:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 0 5) 8000 (endpointMeanRuns 0 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 0 5, EndpointRunConditions (endpointMeanCutoff 0 5) (endpointMeanBox 0 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 0 5 h) (endpointMeanCornerA 0 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 5, endpointJoint24Q (endpointMeanCornerK 0 5 h) (endpointMeanCornerA 0 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 0 5, endpointRunWeightQ (endpointMeanCutoff 0 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 0 5) = (457176113/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 0 5 h = (logRoundedQ ((endpointMeanCutoff 0 5:ℚ)/200)).2+(457176113/1000000000000000:ℚ)+((endpointMeanRuns 0 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 0 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 0 5) r*endpointJoint24Q (endpointMeanCornerK 0 5 h) (endpointMeanCornerA 0 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 0 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 0 5 h≤endpointMeanCorner 0 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 0 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint00_05

namespace EndpointAnalyticJoint00_06
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.leaf (150931299400000:ℤ)) (.branch 2490 (.leaf (1463973900000:ℤ)) (.leaf (2366300500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 171 (.leaf (1867697282344108:ℤ)) (.branch 200 (.leaf (2421865002208065:ℤ)) (.leaf (2831907986321059:ℤ)))), (.branch 171 (.leaf (1872280707928798:ℤ)) (.branch 200 (.leaf (2433817201546767:ℤ)) (.leaf (2851302189988507:ℤ)))), (.branch 171 (.leaf (1869232791371098:ℤ)) (.branch 200 (.leaf (2426053592857446:ℤ)) (.leaf (2838889863916612:ℤ)))), (.branch 171 (.leaf (1874076654388613:ℤ)) (.branch 200 (.leaf (2438728714470612:ℤ)) (.leaf (2859505181958465:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 0 6) 8000 (endpointMeanRuns 0 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 0 6, EndpointRunConditions (endpointMeanCutoff 0 6) (endpointMeanBox 0 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 0 6 h) (endpointMeanCornerA 0 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 6, endpointJoint24Q (endpointMeanCornerK 0 6 h) (endpointMeanCornerA 0 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 0 6, endpointRunWeightQ (endpointMeanCutoff 0 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 0 6) = (456115123/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 0 6 h = (logRoundedQ ((endpointMeanCutoff 0 6:ℚ)/200)).2+(456115123/1000000000000000:ℚ)+((endpointMeanRuns 0 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 0 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 0 6) r*endpointJoint24Q (endpointMeanCornerK 0 6 h) (endpointMeanCornerA 0 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 0 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 0 6 h≤endpointMeanCorner 0 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 0 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint00_06

namespace EndpointAnalyticJoint00_07
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.leaf (147669844400000:ℤ)) (.branch 2490 (.leaf (1458631900000:ℤ)) (.leaf (2358743800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 171 (.leaf (1872280707928798:ℤ)) (.branch 200 (.leaf (2433817201546767:ℤ)) (.leaf (2851302189988507:ℤ)))), (.branch 171 (.leaf (1876875381476575:ℤ)) (.branch 200 (.leaf (2445828386447793:ℤ)) (.leaf (2870829214050441:ℤ)))), (.branch 171 (.leaf (1874076654388613:ℤ)) (.branch 200 (.leaf (2438728714470612:ℤ)) (.leaf (2859505181958465:ℤ)))), (.branch 171 (.leaf (1878933069619550:ℤ)) (.branch 200 (.leaf (2451470058325688:ℤ)) (.leaf (2880270203355622:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 0 7) 8000 (endpointMeanRuns 0 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 0 7, EndpointRunConditions (endpointMeanCutoff 0 7) (endpointMeanBox 0 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 0 7 h) (endpointMeanCornerA 0 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 7, endpointJoint24Q (endpointMeanCornerK 0 7 h) (endpointMeanCornerA 0 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 0 7, endpointRunWeightQ (endpointMeanCutoff 0 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 0 7) = (227531911/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 0 7 h = (logRoundedQ ((endpointMeanCutoff 0 7:ℚ)/200)).2+(227531911/500000000000000:ℚ)+((endpointMeanRuns 0 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 0 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 0 7) r*endpointJoint24Q (endpointMeanCornerK 0 7 h) (endpointMeanCornerA 0 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 0 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 0 7 h≤endpointMeanCorner 0 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 0 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint00_07

namespace EndpointAnalyticJoint00_08
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.leaf (145272254900000:ℤ)) (.branch 2490 (.leaf (1454657300000:ℤ)) (.leaf (2353121200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 171 (.leaf (1876875381476575:ℤ)) (.branch 200 (.leaf (2445828386447793:ℤ)) (.leaf (2870829214050441:ℤ)))), (.branch 171 (.leaf (1881481330590522:ℤ)) (.branch 200 (.leaf (2457898848012097:ℤ)) (.leaf (2890489968121797:ℤ)))), (.branch 171 (.leaf (1878933069619550:ℤ)) (.branch 200 (.leaf (2451470058325688:ℤ)) (.leaf (2880270203355622:ℤ)))), (.branch 171 (.leaf (1883802069591266:ℤ)) (.branch 200 (.leaf (2464277970406353:ℤ)) (.leaf (2901186015216929:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 0 8) 8000 (endpointMeanRuns 0 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 0 8, EndpointRunConditions (endpointMeanCutoff 0 8) (endpointMeanBox 0 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 0 8 h) (endpointMeanCornerA 0 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 8, endpointJoint24Q (endpointMeanCornerK 0 8 h) (endpointMeanCornerA 0 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 0 8, endpointRunWeightQ (endpointMeanCutoff 0 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 0 8) = (141963/312500000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 0 8 h = (logRoundedQ ((endpointMeanCutoff 0 8:ℚ)/200)).2+(141963/312500000000:ℚ)+((endpointMeanRuns 0 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 0 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 0 8) r*endpointJoint24Q (endpointMeanCornerK 0 8 h) (endpointMeanCornerA 0 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 0 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 0 8 h≤endpointMeanCorner 0 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 0 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint00_08

namespace EndpointAnalyticJoint00_09
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.leaf (142138684600000:ℤ)) (.branch 3048 (.leaf (2924251600000:ℤ)) (.leaf (455243800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 158 (.leaf (1881481330590522:ℤ)) (.branch 200 (.leaf (2287827439232770:ℤ)) (.leaf (2890489968121797:ℤ)))), (.branch 158 (.leaf (1886098582941458:ℤ)) (.branch 200 (.leaf (2297406144025005:ℤ)) (.leaf (2910285368046952:ℤ)))), (.branch 158 (.leaf (1883802069591266:ℤ)) (.branch 200 (.leaf (2292804420554674:ℤ)) (.leaf (2901186015216929:ℤ)))), (.branch 158 (.leaf (1888683686915410:ℤ)) (.branch 200 (.leaf (2302959946958790:ℤ)) (.leaf (2922253712545542:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 0 9) 8000 (endpointMeanRuns 0 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 0 9, EndpointRunConditions (endpointMeanCutoff 0 9) (endpointMeanBox 0 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 0 9 h) (endpointMeanCornerA 0 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 9, endpointJoint24Q (endpointMeanCornerK 0 9 h) (endpointMeanCornerA 0 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 0 9, endpointRunWeightQ (endpointMeanCutoff 0 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 0 9) = (453246837/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 0 9 h = (logRoundedQ ((endpointMeanCutoff 0 9:ℚ)/200)).2+(453246837/1000000000000000:ℚ)+((endpointMeanRuns 0 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 0 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 0 9) r*endpointJoint24Q (endpointMeanCornerK 0 9 h) (endpointMeanCornerA 0 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 0 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 0 9 h≤endpointMeanCorner 0 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 0 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint00_09

namespace EndpointAnalyticJoint00_10
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.leaf (139075743200000:ℤ)) (.branch 2490 (.leaf (1444188300000:ℤ)) (.leaf (2338311700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 171 (.leaf (1886098582941458:ℤ)) (.branch 200 (.leaf (2470028878777234:ℤ)) (.leaf (2910285368046952:ℤ)))), (.branch 171 (.leaf (1890727166268116:ℤ)) (.branch 200 (.leaf (2482218772724496:ℤ)) (.leaf (2930216335942425:ℤ)))), (.branch 171 (.leaf (1888683686915410:ℤ)) (.branch 200 (.leaf (2477152798503928:ℤ)) (.leaf (2922253712545542:ℤ)))), (.branch 171 (.leaf (1893577954288132:ℤ)) (.branch 200 (.leaf (2490094892226785:ℤ)) (.leaf (2943474398296276:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 0 10) 8000 (endpointMeanRuns 0 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 0 10, EndpointRunConditions (endpointMeanCutoff 0 10) (endpointMeanBox 0 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 0 10 h) (endpointMeanCornerA 0 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 0 10, endpointJoint24Q (endpointMeanCornerK 0 10 h) (endpointMeanCornerA 0 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 0 10, endpointRunWeightQ (endpointMeanCutoff 0 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 0 10) = (113055323/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 0 10 h = (logRoundedQ ((endpointMeanCutoff 0 10:ℚ)/200)).2+(113055323/250000000000000:ℚ)+((endpointMeanRuns 0 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 0 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 0 10) r*endpointJoint24Q (endpointMeanCornerK 0 10 h) (endpointMeanCornerA 0 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 0 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 0 10 h≤endpointMeanCorner 0 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 0 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint00_10

namespace EndpointAnalyticJoint01_00
private noncomputable def weights : IntegerLookupTree := (.branch 1688 (.leaf (170099760000000:ℤ)) (.branch 2961 (.leaf (4269743300000:ℤ)) (.leaf (655374200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.leaf (1834626626206955:ℤ)) (.branch 200 (.leaf (2199336339141089:ℤ)) (.leaf (2732549366383132:ℤ)))), (.branch 157 (.leaf (1835917768030866:ℤ)) (.branch 200 (.leaf (2201990120599560:ℤ)) (.leaf (2738021320692754:ℤ)))), (.branch 157 (.leaf (1834808223742031:ℤ)) (.branch 200 (.leaf (2199723598466255:ℤ)) (.leaf (2733384294732937:ℤ)))), (.branch 157 (.leaf (1836168942666535:ℤ)) (.branch 200 (.leaf (2202526031136784:ℤ)) (.leaf (2739177687066976:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 1 0) 8000 (endpointMeanRuns 1 0) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 1 0, EndpointRunConditions (endpointMeanCutoff 1 0) (endpointMeanBox 1 0).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 0, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 1 0 h) (endpointMeanCornerA 1 0 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 0, endpointJoint24Q (endpointMeanCornerK 1 0 h) (endpointMeanCornerA 1 0 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 1 0, endpointRunWeightQ (endpointMeanCutoff 1 0) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 1 0) = (462075431/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 1 0 h = (logRoundedQ ((endpointMeanCutoff 1 0:ℚ)/200)).2+(462075431/1000000000000000:ℚ)+((endpointMeanRuns 1 0).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 1 0).map (fun r => endpointRunWeightQ (endpointMeanCutoff 1 0) r*endpointJoint24Q (endpointMeanCornerK 1 0 h) (endpointMeanCornerA 1 0 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 1 0).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 1 0 h≤endpointMeanCorner 1 0 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 1 0 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint01_00

namespace EndpointAnalyticJoint01_01
private noncomputable def weights : IntegerLookupTree := (.branch 1688 (.leaf (168238484800000:ℤ)) (.branch 2961 (.leaf (4261624400000:ℤ)) (.leaf (654344900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.leaf (1835917768030866:ℤ)) (.branch 200 (.leaf (2201990120599560:ℤ)) (.leaf (2738021320692754:ℤ)))), (.branch 157 (.leaf (1840595213819426:ℤ)) (.branch 200 (.leaf (2211615189284357:ℤ)) (.leaf (2757904156250725:ℤ)))), (.branch 157 (.leaf (1836168942666535:ℤ)) (.branch 200 (.leaf (2202526031136784:ℤ)) (.leaf (2739177687066976:ℤ)))), (.branch 157 (.leaf (1841098877398496:ℤ)) (.branch 200 (.leaf (2212691826369029:ℤ)) (.leaf (2760234175416214:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 1 1) 8000 (endpointMeanRuns 1 1) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 1 1, EndpointRunConditions (endpointMeanCutoff 1 1) (endpointMeanBox 1 1).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 1, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 1 1 h) (endpointMeanCornerA 1 1 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 1, endpointJoint24Q (endpointMeanCornerK 1 1 h) (endpointMeanCornerA 1 1 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 1 1, endpointRunWeightQ (endpointMeanCutoff 1 1) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 1 1) = (461520651/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 1 1 h = (logRoundedQ ((endpointMeanCutoff 1 1:ℚ)/200)).2+(461520651/1000000000000000:ℚ)+((endpointMeanRuns 1 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 1 1).map (fun r => endpointRunWeightQ (endpointMeanCutoff 1 1) r*endpointJoint24Q (endpointMeanCornerK 1 1 h) (endpointMeanCornerA 1 1 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 1 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 1 1 h≤endpointMeanCorner 1 1 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 1 1 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint01_01

namespace EndpointAnalyticJoint01_02
private noncomputable def weights : IntegerLookupTree := (.branch 1688 (.leaf (164579967000000:ℤ)) (.branch 2961 (.leaf (4245503100000:ℤ)) (.leaf (652301000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.leaf (1840595213819426:ℤ)) (.branch 200 (.leaf (2211615189284357:ℤ)) (.leaf (2757904156250725:ℤ)))), (.branch 157 (.leaf (1845284576535573:ℤ)) (.branch 200 (.leaf (2221282329886879:ℤ)) (.leaf (2777931376056858:ℤ)))), (.branch 157 (.leaf (1841098877398496:ℤ)) (.branch 200 (.leaf (2212691826369029:ℤ)) (.leaf (2760234175416214:ℤ)))), (.branch 157 (.leaf (1846042048524935:ℤ)) (.branch 200 (.leaf (2222904541996873:ℤ)) (.leaf (2781452528292788:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 1 2) 8000 (endpointMeanRuns 1 2) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 1 2, EndpointRunConditions (endpointMeanCutoff 1 2) (endpointMeanBox 1 2).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 2, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 1 2 h) (endpointMeanCornerA 1 2 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 2, endpointJoint24Q (endpointMeanCornerK 1 2 h) (endpointMeanCornerA 1 2 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 1 2, endpointRunWeightQ (endpointMeanCutoff 1 2) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 1 2) = (460419049/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 1 2 h = (logRoundedQ ((endpointMeanCutoff 1 2:ℚ)/200)).2+(460419049/1000000000000000:ℚ)+((endpointMeanRuns 1 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 1 2).map (fun r => endpointRunWeightQ (endpointMeanCutoff 1 2) r*endpointJoint24Q (endpointMeanCornerK 1 2 h) (endpointMeanCornerA 1 2 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 1 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 1 2 h≤endpointMeanCorner 1 2 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 1 2 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint01_02

namespace EndpointAnalyticJoint01_03
private noncomputable def weights : IntegerLookupTree := (.branch 1688 (.leaf (161005044100000:ℤ)) (.branch 2961 (.leaf (4229534600000:ℤ)) (.leaf (650276400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.leaf (1845284576535573:ℤ)) (.branch 200 (.leaf (2221282329886879:ℤ)) (.leaf (2777931376056858:ℤ)))), (.branch 157 (.leaf (1849985886540577:ℤ)) (.branch 200 (.leaf (2230991726306722:ℤ)) (.leaf (2798104028593948:ℤ)))), (.branch 157 (.leaf (1846042048524935:ℤ)) (.branch 200 (.leaf (2222904541996873:ℤ)) (.leaf (2781452528292788:ℤ)))), (.branch 157 (.leaf (1850998491584287:ℤ)) (.branch 200 (.leaf (2233164394582175:ℤ)) (.leaf (2802833989974693:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 1 3) 8000 (endpointMeanRuns 1 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 1 3, EndpointRunConditions (endpointMeanCutoff 1 3) (endpointMeanBox 1 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 1 3 h) (endpointMeanCornerA 1 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 3, endpointJoint24Q (endpointMeanCornerK 1 3 h) (endpointMeanCornerA 1 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 1 3, endpointRunWeightQ (endpointMeanCutoff 1 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 1 3) = (28707993/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 1 3 h = (logRoundedQ ((endpointMeanCutoff 1 3:ℚ)/200)).2+(28707993/62500000000000:ℚ)+((endpointMeanRuns 1 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 1 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 1 3) r*endpointJoint24Q (endpointMeanCornerK 1 3 h) (endpointMeanCornerA 1 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 1 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 1 3 h≤endpointMeanCorner 1 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 1 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint01_03

namespace EndpointAnalyticJoint01_04
private noncomputable def weights : IntegerLookupTree := (.branch 1688 (.leaf (157511631500000:ℤ)) (.branch 2961 (.leaf (4213716000000:ℤ)) (.leaf (648270900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.leaf (1849985886540577:ℤ)) (.branch 200 (.leaf (2230991726306722:ℤ)) (.leaf (2798104028593948:ℤ)))), (.branch 157 (.leaf (1854699174273051:ℤ)) (.branch 200 (.leaf (2240743563247330:ℤ)) (.leaf (2818423169958618:ℤ)))), (.branch 157 (.leaf (1850998491584287:ℤ)) (.branch 200 (.leaf (2233164394582175:ℤ)) (.leaf (2802833989974693:ℤ)))), (.branch 157 (.leaf (1855968242210400:ℤ)) (.branch 200 (.leaf (2243471601686351:ℤ)) (.leaf (2824379814304895:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 1 4) 8000 (endpointMeanRuns 1 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 1 4, EndpointRunConditions (endpointMeanCutoff 1 4) (endpointMeanBox 1 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 1 4 h) (endpointMeanCornerA 1 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 4, endpointJoint24Q (endpointMeanCornerK 1 4 h) (endpointMeanCornerA 1 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 1 4, endpointRunWeightQ (endpointMeanCutoff 1 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 1 4) = (458246973/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 1 4 h = (logRoundedQ ((endpointMeanCutoff 1 4:ℚ)/200)).2+(458246973/1000000000000000:ℚ)+((endpointMeanRuns 1 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 1 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 1 4) r*endpointJoint24Q (endpointMeanCornerK 1 4 h) (endpointMeanCornerA 1 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 1 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 1 4 h≤endpointMeanCorner 1 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 1 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint01_04

namespace EndpointAnalyticJoint01_05
private noncomputable def weights : IntegerLookupTree := (.branch 1688 (.leaf (154097704400000:ℤ)) (.branch 2961 (.leaf (4198044600000:ℤ)) (.leaf (646284000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.leaf (1854699174273051:ℤ)) (.branch 200 (.leaf (2240743563247330:ℤ)) (.leaf (2818423169958618:ℤ)))), (.branch 157 (.leaf (1859424470249162:ℤ)) (.branch 200 (.leaf (2250538026219485:ℤ)) (.leaf (2838889863916612:ℤ)))), (.branch 157 (.leaf (1855968242210400:ℤ)) (.branch 200 (.leaf (2243471601686351:ℤ)) (.leaf (2824379814304895:ℤ)))), (.branch 157 (.leaf (1860951336132789:ℤ)) (.branch 200 (.leaf (2253826381874957:ℤ)) (.leaf (2846091264764839:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 1 5) 8000 (endpointMeanRuns 1 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 1 5, EndpointRunConditions (endpointMeanCutoff 1 5) (endpointMeanBox 1 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 1 5 h) (endpointMeanCornerA 1 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 5, endpointJoint24Q (endpointMeanCornerK 1 5 h) (endpointMeanCornerA 1 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 1 5, endpointRunWeightQ (endpointMeanCutoff 1 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 1 5) = (457176113/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 1 5 h = (logRoundedQ ((endpointMeanCutoff 1 5:ℚ)/200)).2+(457176113/1000000000000000:ℚ)+((endpointMeanRuns 1 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 1 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 1 5) r*endpointJoint24Q (endpointMeanCornerK 1 5 h) (endpointMeanCornerA 1 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 1 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 1 5 h≤endpointMeanCorner 1 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 1 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint01_05

namespace EndpointAnalyticJoint01_06
private noncomputable def weights : IntegerLookupTree := (.branch 1688 (.leaf (150761295900000:ℤ)) (.branch 2961 (.leaf (4182517600000:ℤ)) (.leaf (644315500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.leaf (1859424470249162:ℤ)) (.branch 200 (.leaf (2250538026219485:ℤ)) (.leaf (2838889863916612:ℤ)))), (.branch 157 (.leaf (1864161805062819:ℤ)) (.branch 200 (.leaf (2260375301544863:ℤ)) (.leaf (2859505181958465:ℤ)))), (.branch 157 (.leaf (1860951336132789:ℤ)) (.branch 200 (.leaf (2253826381874957:ℤ)) (.leaf (2846091264764839:ℤ)))), (.branch 157 (.leaf (1865947809176912:ℤ)) (.branch 200 (.leaf (2264228954722341:ℤ)) (.leaf (2867969614548549:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 1 6) 8000 (endpointMeanRuns 1 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 1 6, EndpointRunConditions (endpointMeanCutoff 1 6) (endpointMeanBox 1 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 1 6 h) (endpointMeanCornerA 1 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 6, endpointJoint24Q (endpointMeanCornerK 1 6 h) (endpointMeanCornerA 1 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 1 6, endpointRunWeightQ (endpointMeanCutoff 1 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 1 6) = (456115123/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 1 6 h = (logRoundedQ ((endpointMeanCutoff 1 6:ℚ)/200)).2+(456115123/1000000000000000:ℚ)+((endpointMeanRuns 1 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 1 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 1 6) r*endpointJoint24Q (endpointMeanCornerK 1 6 h) (endpointMeanCornerA 1 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 1 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 1 6 h≤endpointMeanCorner 1 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 1 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint01_06

namespace EndpointAnalyticJoint01_07
private noncomputable def weights : IntegerLookupTree := (.branch 1688 (.leaf (147500494700000:ℤ)) (.branch 2961 (.leaf (4167132400000:ℤ)) (.leaf (642364900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.leaf (1864161805062819:ℤ)) (.branch 200 (.leaf (2260375301544863:ℤ)) (.leaf (2859505181958465:ℤ)))), (.branch 157 (.leaf (1868911209385888:ℤ)) (.branch 200 (.leaf (2270255576359566:ℤ)) (.leaf (2880270203355622:ℤ)))), (.branch 157 (.leaf (1865947809176912:ℤ)) (.branch 200 (.leaf (2264228954722341:ℤ)) (.leaf (2867969614548549:ℤ)))), (.branch 157 (.leaf (1870957697264402:ℤ)) (.branch 200 (.leaf (2274679540816318:ℤ)) (.leaf (2890016146637299:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 1 7) 8000 (endpointMeanRuns 1 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 1 7, EndpointRunConditions (endpointMeanCutoff 1 7) (endpointMeanBox 1 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 1 7 h) (endpointMeanCornerA 1 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 7, endpointJoint24Q (endpointMeanCornerK 1 7 h) (endpointMeanCornerA 1 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 1 7, endpointRunWeightQ (endpointMeanCutoff 1 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 1 7) = (227531911/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 1 7 h = (logRoundedQ ((endpointMeanCutoff 1 7:ℚ)/200)).2+(227531911/500000000000000:ℚ)+((endpointMeanRuns 1 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 1 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 1 7) r*endpointJoint24Q (endpointMeanCornerK 1 7 h) (endpointMeanCornerA 1 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 1 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 1 7 h≤endpointMeanCorner 1 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 1 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint01_07

namespace EndpointAnalyticJoint01_08
private noncomputable def weights : IntegerLookupTree := (.branch 1688 (.leaf (144313443200000:ℤ)) (.branch 3125 (.leaf (4824191300000:ℤ)) (.leaf (396341900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 154 (.leaf (1868911209385888:ℤ)) (.branch 200 (.leaf (2233390620500916:ℤ)) (.leaf (2880270203355622:ℤ)))), (.branch 154 (.leaf (1873672713968362:ℤ)) (.branch 200 (.leaf (2242768408476566:ℤ)) (.leaf (2901186015216929:ℤ)))), (.branch 154 (.leaf (1870957697264402:ℤ)) (.branch 200 (.leaf (2237558536028454:ℤ)) (.leaf (2890016146637299:ℤ)))), (.branch 154 (.leaf (1875981036413342:ℤ)) (.branch 200 (.leaf (2247477550591584:ℤ)) (.leaf (2912232153874834:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 1 8) 8000 (endpointMeanRuns 1 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 1 8, EndpointRunConditions (endpointMeanCutoff 1 8) (endpointMeanBox 1 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 1 8 h) (endpointMeanCornerA 1 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 8, endpointJoint24Q (endpointMeanCornerK 1 8 h) (endpointMeanCornerA 1 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 1 8, endpointRunWeightQ (endpointMeanCutoff 1 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 1 8) = (113505509/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 1 8 h = (logRoundedQ ((endpointMeanCutoff 1 8:ℚ)/200)).2+(113505509/250000000000000:ℚ)+((endpointMeanRuns 1 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 1 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 1 8) r*endpointJoint24Q (endpointMeanCornerK 1 8 h) (endpointMeanCornerA 1 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 1 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 1 8 h≤endpointMeanCorner 1 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 1 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint01_08

namespace EndpointAnalyticJoint01_09
private noncomputable def weights : IntegerLookupTree := (.branch 1688 (.leaf (141198335900000:ℤ)) (.branch 2961 (.leaf (4136777200000:ℤ)) (.leaf (638516400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.leaf (1873672713968362:ℤ)) (.branch 200 (.leaf (2280179038617678:ℤ)) (.leaf (2901186015216929:ℤ)))), (.branch 157 (.leaf (1878446349638598:ℤ)) (.branch 200 (.leaf (2290145877094838:ℤ)) (.leaf (2922253712545542:ℤ)))), (.branch 157 (.leaf (1875981036413342:ℤ)) (.branch 200 (.leaf (2285178361762819:ℤ)) (.leaf (2912232153874834:ℤ)))), (.branch 157 (.leaf (1881017862738527:ℤ)) (.branch 200 (.leaf (2295725640190598:ℤ)) (.leaf (2934618939043199:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 1 9) 8000 (endpointMeanRuns 1 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 1 9, EndpointRunConditions (endpointMeanCutoff 1 9) (endpointMeanBox 1 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 1 9 h) (endpointMeanCornerA 1 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 9, endpointJoint24Q (endpointMeanCornerK 1 9 h) (endpointMeanCornerA 1 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 1 9, endpointRunWeightQ (endpointMeanCutoff 1 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 1 9) = (452989593/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 1 9 h = (logRoundedQ ((endpointMeanCutoff 1 9:ℚ)/200)).2+(452989593/1000000000000000:ℚ)+((endpointMeanRuns 1 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 1 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 1 9) r*endpointJoint24Q (endpointMeanCornerK 1 9 h) (endpointMeanCornerA 1 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 1 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 1 9 h≤endpointMeanCorner 1 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 1 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint01_09

namespace EndpointAnalyticJoint01_10
private noncomputable def weights : IntegerLookupTree := (.branch 1688 (.leaf (138153417500000:ℤ)) (.branch 2961 (.leaf (4121802300000:ℤ)) (.leaf (636617800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.leaf (1878446349638598:ℤ)) (.branch 200 (.leaf (2290145877094838:ℤ)) (.leaf (2922253712545542:ℤ)))), (.branch 157 (.leaf (1883232147303475:ℤ)) (.branch 200 (.leaf (2300156281391858:ℤ)) (.leaf (2943474398296276:ℤ)))), (.branch 157 (.leaf (1881017862738527:ℤ)) (.branch 200 (.leaf (2295725640190598:ℤ)) (.leaf (2934618939043199:ℤ)))), (.branch 157 (.leaf (1886068212451708:ℤ)) (.branch 200 (.leaf (2306321599755962:ℤ)) (.leaf (2957177814939120:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 1 10) 8000 (endpointMeanRuns 1 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 1 10, EndpointRunConditions (endpointMeanCutoff 1 10) (endpointMeanBox 1 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 1 10 h) (endpointMeanCornerA 1 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 10, endpointJoint24Q (endpointMeanCornerK 1 10 h) (endpointMeanCornerA 1 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 1 10, endpointRunWeightQ (endpointMeanCutoff 1 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 1 10) = (451966327/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 1 10 h = (logRoundedQ ((endpointMeanCutoff 1 10:ℚ)/200)).2+(451966327/1000000000000000:ℚ)+((endpointMeanRuns 1 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 1 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 1 10) r*endpointJoint24Q (endpointMeanCornerK 1 10 h) (endpointMeanCornerA 1 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 1 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 1 10 h≤endpointMeanCorner 1 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 1 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint01_10

namespace EndpointAnalyticJoint01_11
private noncomputable def weights : IntegerLookupTree := (.branch 1688 (.leaf (135914761700000:ℤ)) (.branch 2961 (.leaf (4110657800000:ℤ)) (.leaf (635204900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.leaf (1883232147303475:ℤ)) (.branch 200 (.leaf (2300156281391858:ℤ)) (.leaf (2943474398296276:ℤ)))), (.branch 157 (.leaf (1888030137948628:ℤ)) (.branch 200 (.leaf (2310210441938286:ℤ)) (.leaf (2964849183433315:ℤ)))), (.branch 157 (.leaf (1886068212451708:ℤ)) (.branch 200 (.leaf (2306321599755962:ℤ)) (.leaf (2957177814939120:ℤ)))), (.branch 157 (.leaf (1891132121861863:ℤ)) (.branch 200 (.leaf (2316966465147507:ℤ)) (.leaf (2979910104450998:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 1 11) 8000 (endpointMeanRuns 1 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 1 11, EndpointRunConditions (endpointMeanCutoff 1 11) (endpointMeanBox 1 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 1 11 h) (endpointMeanCornerA 1 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 1 11, endpointJoint24Q (endpointMeanCornerK 1 11 h) (endpointMeanCornerA 1 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 1 11, endpointRunWeightQ (endpointMeanCutoff 1 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 1 11) = (451204803/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 1 11 h = (logRoundedQ ((endpointMeanCutoff 1 11:ℚ)/200)).2+(451204803/1000000000000000:ℚ)+((endpointMeanRuns 1 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 1 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 1 11) r*endpointJoint24Q (endpointMeanCornerK 1 11 h) (endpointMeanCornerA 1 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 1 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 1 11 h≤endpointMeanCorner 1 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 1 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint01_11

namespace EndpointAnalyticJoint02_00
private noncomputable def weights : IntegerLookupTree := (.branch 1614 (.leaf (170806790600000:ℤ)) (.branch 3046 (.leaf (6812106000000:ℤ)) (.leaf (556618300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 153 (.leaf (1826118356728202:ℤ)) (.branch 200 (.leaf (2156809103538734:ℤ)) (.leaf (2735653371564601:ℤ)))), (.branch 153 (.leaf (1826927747598062:ℤ)) (.branch 200 (.leaf (2158391937745237:ℤ)) (.leaf (2739177687066976:ℤ)))), (.branch 153 (.leaf (1826326027060233:ℤ)) (.branch 200 (.leaf (2157230611738402:ℤ)) (.leaf (2736643822566546:ℤ)))), (.branch 153 (.leaf (1827177502387305:ℤ)) (.branch 200 (.leaf (2158899016170567:ℤ)) (.leaf (2740369889345232:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 2 0) 8000 (endpointMeanRuns 2 0) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 2 0, EndpointRunConditions (endpointMeanCutoff 2 0) (endpointMeanBox 2 0).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 0, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 2 0 h) (endpointMeanCornerA 2 0 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 0, endpointJoint24Q (endpointMeanCornerK 2 0 h) (endpointMeanCornerA 2 0 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 2 0, endpointRunWeightQ (endpointMeanCutoff 2 0) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 2 0) = (462353827/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 2 0 h = (logRoundedQ ((endpointMeanCutoff 2 0:ℚ)/200)).2+(462353827/1000000000000000:ℚ)+((endpointMeanRuns 2 0).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 2 0).map (fun r => endpointRunWeightQ (endpointMeanCutoff 2 0) r*endpointJoint24Q (endpointMeanCornerK 2 0 h) (endpointMeanCornerA 2 0 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 2 0).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 2 0 h≤endpointMeanCorner 2 0 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 2 0 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint02_00

namespace EndpointAnalyticJoint02_01
private noncomputable def weights : IntegerLookupTree := (.branch 1614 (.leaf (168007457900000:ℤ)) (.branch 2882 (.leaf (5876417500000:ℤ)) (.leaf (893507200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 156 (.leaf (1826927747598062:ℤ)) (.branch 200 (.leaf (2191407165939335:ℤ)) (.leaf (2739177687066976:ℤ)))), (.branch 156 (.leaf (1831749386608808:ℤ)) (.branch 200 (.leaf (2201387312083701:ℤ)) (.leaf (2760234175416214:ℤ)))), (.branch 156 (.leaf (1827177502387305:ℤ)) (.branch 200 (.leaf (2191945124170259:ℤ)) (.leaf (2740369889345232:ℤ)))), (.branch 156 (.leaf (1832250248729536:ℤ)) (.branch 200 (.leaf (2202468261166022:ℤ)) (.leaf (2762637432148464:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 2 1) 8000 (endpointMeanRuns 2 1) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 2 1, EndpointRunConditions (endpointMeanCutoff 2 1) (endpointMeanBox 2 1).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 1, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 2 1 h) (endpointMeanCornerA 2 1 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 1, endpointJoint24Q (endpointMeanCornerK 2 1 h) (endpointMeanCornerA 2 1 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 2 1, endpointRunWeightQ (endpointMeanCutoff 2 1) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 2 1) = (461520651/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 2 1 h = (logRoundedQ ((endpointMeanCutoff 2 1:ℚ)/200)).2+(461520651/1000000000000000:ℚ)+((endpointMeanRuns 2 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 2 1).map (fun r => endpointRunWeightQ (endpointMeanCutoff 2 1) r*endpointJoint24Q (endpointMeanCornerK 2 1 h) (endpointMeanCornerA 2 1 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 2 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 2 1 h≤endpointMeanCorner 2 1 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 2 1 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint02_01

namespace EndpointAnalyticJoint02_02
private noncomputable def weights : IntegerLookupTree := (.branch 1614 (.leaf (164349870500000:ℤ)) (.branch 2882 (.leaf (5853840100000:ℤ)) (.leaf (890694400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 156 (.leaf (1831749386608808:ℤ)) (.branch 200 (.leaf (2201387312083701:ℤ)) (.leaf (2760234175416214:ℤ)))), (.branch 156 (.leaf (1836583750919048:ℤ)) (.branch 200 (.leaf (2211412909990117:ℤ)) (.leaf (2781452528292788:ℤ)))), (.branch 156 (.leaf (1832250248729536:ℤ)) (.branch 200 (.leaf (2202468261166022:ℤ)) (.leaf (2762637432148464:ℤ)))), (.branch 156 (.leaf (1837337078408177:ℤ)) (.branch 200 (.leaf (2213041917862760:ℤ)) (.leaf (2785085915292786:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 2 2) 8000 (endpointMeanRuns 2 2) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 2 2, EndpointRunConditions (endpointMeanCutoff 2 2) (endpointMeanBox 2 2).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 2, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 2 2 h) (endpointMeanCornerA 2 2 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 2, endpointJoint24Q (endpointMeanCornerK 2 2 h) (endpointMeanCornerA 2 2 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 2 2, endpointRunWeightQ (endpointMeanCutoff 2 2) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 2 2) = (460419049/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 2 2 h = (logRoundedQ ((endpointMeanCutoff 2 2:ℚ)/200)).2+(460419049/1000000000000000:ℚ)+((endpointMeanRuns 2 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 2 2).map (fun r => endpointRunWeightQ (endpointMeanCutoff 2 2) r*endpointJoint24Q (endpointMeanCornerK 2 2 h) (endpointMeanCornerA 2 2 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 2 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 2 2 h≤endpointMeanCorner 2 2 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 2 2 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint02_02

namespace EndpointAnalyticJoint02_03
private noncomputable def weights : IntegerLookupTree := (.branch 1614 (.leaf (160775869100000:ℤ)) (.branch 3046 (.leaf (6740530500000:ℤ)) (.leaf (551894500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 153 (.leaf (1836583750919048:ℤ)) (.branch 200 (.leaf (2177310530406862:ℤ)) (.leaf (2781452528292788:ℤ)))), (.branch 153 (.leaf (1841430874113485:ℤ)) (.branch 200 (.leaf (2186831920186811:ℤ)) (.leaf (2802833989974693:ℤ)))), (.branch 153 (.leaf (1837337078408177:ℤ)) (.branch 200 (.leaf (2178845460062381:ℤ)) (.leaf (2785085915292786:ℤ)))), (.branch 153 (.leaf (1842438030522443:ℤ)) (.branch 200 (.leaf (2188887684208581:ℤ)) (.leaf (2807716809053002:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 2 3) 8000 (endpointMeanRuns 2 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 2 3, EndpointRunConditions (endpointMeanCutoff 2 3) (endpointMeanBox 2 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 2 3 h) (endpointMeanCornerA 2 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 3, endpointJoint24Q (endpointMeanCornerK 2 3 h) (endpointMeanCornerA 2 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 2 3, endpointRunWeightQ (endpointMeanCutoff 2 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 2 3) = (28707993/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 2 3 h = (logRoundedQ ((endpointMeanCutoff 2 3:ℚ)/200)).2+(28707993/62500000000000:ℚ)+((endpointMeanRuns 2 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 2 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 2 3) r*endpointJoint24Q (endpointMeanCornerK 2 3 h) (endpointMeanCornerA 2 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 2 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 2 3 h≤endpointMeanCorner 2 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 2 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint02_03

namespace EndpointAnalyticJoint02_04
private noncomputable def weights : IntegerLookupTree := (.branch 1614 (.leaf (157283369300000:ℤ)) (.branch 2882 (.leaf (5809323300000:ℤ)) (.leaf (885148400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 156 (.leaf (1841430874113485:ℤ)) (.branch 200 (.leaf (2221484166655824:ℤ)) (.leaf (2802833989974693:ℤ)))), (.branch 156 (.leaf (1846290789865429:ℤ)) (.branch 200 (.leaf (2231601290020762:ℤ)) (.leaf (2824379814304895:ℤ)))), (.branch 156 (.leaf (1842438030522443:ℤ)) (.branch 200 (.leaf (2223666336796542:ℤ)) (.leaf (2807716809053002:ℤ)))), (.branch 156 (.leaf (1847553144280086:ℤ)) (.branch 200 (.leaf (2234341761667788:ℤ)) (.leaf (2830531595650986:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 2 4) 8000 (endpointMeanRuns 2 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 2 4, EndpointRunConditions (endpointMeanCutoff 2 4) (endpointMeanBox 2 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 2 4 h) (endpointMeanCornerA 2 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 4, endpointJoint24Q (endpointMeanCornerK 2 4 h) (endpointMeanCornerA 2 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 2 4, endpointRunWeightQ (endpointMeanCutoff 2 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 2 4) = (458246973/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 2 4 h = (logRoundedQ ((endpointMeanCutoff 2 4:ℚ)/200)).2+(458246973/1000000000000000:ℚ)+((endpointMeanRuns 2 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 2 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 2 4) r*endpointJoint24Q (endpointMeanCornerK 2 4 h) (endpointMeanCornerA 2 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 2 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 2 4 h≤endpointMeanCorner 2 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 2 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint02_04

namespace EndpointAnalyticJoint02_05
private noncomputable def weights : IntegerLookupTree := (.branch 1614 (.leaf (153870346600000:ℤ)) (.branch 3046 (.leaf (6689632500000:ℤ)) (.leaf (548535300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 153 (.leaf (1846290789865429:ℤ)) (.branch 200 (.leaf (2196394947051633:ℤ)) (.leaf (2824379814304895:ℤ)))), (.branch 153 (.leaf (1851163531937082:ℤ)) (.branch 200 (.leaf (2205999793080498:ℤ)) (.leaf (2846091264764839:ℤ)))), (.branch 153 (.leaf (1847553144280086:ℤ)) (.branch 200 (.leaf (2198976192622141:ℤ)) (.leaf (2830531595650986:ℤ)))), (.branch 153 (.leaf (1852682458997720:ℤ)) (.branch 200 (.leaf (2209111198625663:ℤ)) (.leaf (2853531769352765:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 2 5) 8000 (endpointMeanRuns 2 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 2 5, EndpointRunConditions (endpointMeanCutoff 2 5) (endpointMeanBox 2 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 2 5 h) (endpointMeanCornerA 2 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 5, endpointJoint24Q (endpointMeanCornerK 2 5 h) (endpointMeanCornerA 2 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 2 5, endpointRunWeightQ (endpointMeanCutoff 2 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 2 5) = (457176113/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 2 5 h = (logRoundedQ ((endpointMeanCutoff 2 5:ℚ)/200)).2+(457176113/1000000000000000:ℚ)+((endpointMeanRuns 2 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 2 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 2 5) r*endpointJoint24Q (endpointMeanCornerK 2 5 h) (endpointMeanCornerA 2 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 2 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 2 5 h≤endpointMeanCorner 2 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 2 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint02_05

namespace EndpointAnalyticJoint02_06
private noncomputable def weights : IntegerLookupTree := (.branch 1614 (.leaf (150534834200000:ℤ)) (.branch 3046 (.leaf (6664535900000:ℤ)) (.leaf (546879000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 153 (.leaf (1851163531937082:ℤ)) (.branch 200 (.leaf (2205999793080498:ℤ)) (.leaf (2846091264764839:ℤ)))), (.branch 153 (.leaf (1856049134179753:ℤ)) (.branch 200 (.leaf (2215646641148828:ℤ)) (.leaf (2867969614548549:ℤ)))), (.branch 153 (.leaf (1852682458997720:ℤ)) (.branch 200 (.leaf (2209111198625663:ℤ)) (.leaf (2853531769352765:ℤ)))), (.branch 153 (.leaf (1857826014101107:ℤ)) (.branch 200 (.leaf (2219292916524944:ℤ)) (.leaf (2876718836566391:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 2 6) 8000 (endpointMeanRuns 2 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 2 6, EndpointRunConditions (endpointMeanCutoff 2 6) (endpointMeanBox 2 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 2 6 h) (endpointMeanCornerA 2 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 6, endpointJoint24Q (endpointMeanCornerK 2 6 h) (endpointMeanCornerA 2 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 2 6, endpointRunWeightQ (endpointMeanCutoff 2 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 2 6) = (456115123/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 2 6 h = (logRoundedQ ((endpointMeanCutoff 2 6:ℚ)/200)).2+(456115123/1000000000000000:ℚ)+((endpointMeanRuns 2 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 2 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 2 6) r*endpointJoint24Q (endpointMeanCornerK 2 6 h) (endpointMeanCornerA 2 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 2 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 2 6 h≤endpointMeanCorner 2 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 2 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint02_06

namespace EndpointAnalyticJoint02_07
private noncomputable def weights : IntegerLookupTree := (.branch 1614 (.leaf (147274920800000:ℤ)) (.branch 3046 (.leaf (6639668500000:ℤ)) (.leaf (545237800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 153 (.leaf (1856049134179753:ℤ)) (.branch 200 (.leaf (2215646641148828:ℤ)) (.leaf (2867969614548549:ℤ)))), (.branch 153 (.leaf (1860947630534075:ℤ)) (.branch 200 (.leaf (2225335674931746:ℤ)) (.leaf (2890016146637299:ℤ)))), (.branch 153 (.leaf (1857826014101107:ℤ)) (.branch 200 (.leaf (2219292916524944:ℤ)) (.leaf (2876718836566391:ℤ)))), (.branch 153 (.leaf (1862983849125463:ℤ)) (.branch 200 (.leaf (2229521561613513:ℤ)) (.leaf (2900094315940609:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 2 7) 8000 (endpointMeanRuns 2 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 2 7, EndpointRunConditions (endpointMeanCutoff 2 7) (endpointMeanBox 2 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 2 7 h) (endpointMeanCornerA 2 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 7, endpointJoint24Q (endpointMeanCornerK 2 7 h) (endpointMeanCornerA 2 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 2 7, endpointRunWeightQ (endpointMeanCutoff 2 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 2 7) = (227531911/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 2 7 h = (logRoundedQ ((endpointMeanCutoff 2 7:ℚ)/200)).2+(227531911/500000000000000:ℚ)+((endpointMeanRuns 2 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 2 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 2 7) r*endpointJoint24Q (endpointMeanCornerK 2 7 h) (endpointMeanCornerA 2 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 2 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 2 7 h≤endpointMeanCorner 2 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 2 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint02_07

namespace EndpointAnalyticJoint02_08
private noncomputable def weights : IntegerLookupTree := (.branch 2018 (.branch 1614 (.leaf (144088749000000:ℤ)) (.leaf (1555646100000:ℤ))) (.branch 3046 (.leaf (1498965500000:ℤ)) (.leaf (543611400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 180 (.branch 153 (.leaf (1860947630534075:ℤ)) (.leaf (2225335674931746:ℤ))) (.branch 200 (.leaf (2583270914368401:ℤ)) (.leaf (2890016146637299:ℤ)))), (.branch 180 (.branch 153 (.leaf (1865859055030274:ℤ)) (.leaf (2235067078907595:ℤ))) (.branch 200 (.leaf (2599160325803822:ℤ)) (.leaf (2912232153874834:ℤ)))), (.branch 180 (.branch 153 (.leaf (1862983849125463:ℤ)) (.leaf (2229521561613513:ℤ))) (.branch 200 (.leaf (2590316905642322:ℤ)) (.leaf (2900094315940609:ℤ)))), (.branch 180 (.branch 153 (.leaf (1868156003715774:ℤ)) (.leaf (2239797350177183:ℤ))) (.branch 200 (.leaf (2607137180998100:ℤ)) (.leaf (2923659738464301:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 2 8) 8000 (endpointMeanRuns 2 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 2 8, EndpointRunConditions (endpointMeanCutoff 2 8) (endpointMeanBox 2 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 2 8 h) (endpointMeanCornerA 2 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 8, endpointJoint24Q (endpointMeanCornerK 2 8 h) (endpointMeanCornerA 2 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 2 8, endpointRunWeightQ (endpointMeanCutoff 2 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 2 8) = (113505509/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 2 8 h = (logRoundedQ ((endpointMeanCutoff 2 8:ℚ)/200)).2+(113505509/250000000000000:ℚ)+((endpointMeanRuns 2 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 2 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 2 8) r*endpointJoint24Q (endpointMeanCornerK 2 8 h) (endpointMeanCornerA 2 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 2 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 2 8 h≤endpointMeanCorner 2 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 2 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint02_08

namespace EndpointAnalyticJoint02_09
private noncomputable def weights : IntegerLookupTree := (.branch 2242 (.branch 1614 (.leaf (140974513700000:ℤ)) (.leaf (2517732200000:ℤ))) (.branch 2882 (.leaf (507079100000:ℤ)) (.leaf (871724600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 172 (.branch 156 (.leaf (1865859055030274:ℤ)) (.leaf (2272532642507654:ℤ))) (.branch 200 (.leaf (2484728721053039:ℤ)) (.leaf (2912232153874834:ℤ)))), (.branch 172 (.branch 156 (.leaf (1870783441788376:ℤ)) (.leaf (2282882251764475:ℤ))) (.branch 200 (.leaf (2498616572705741:ℤ)) (.leaf (2934618939043199:ℤ)))), (.branch 172 (.branch 156 (.leaf (1868156003715774:ℤ)) (.leaf (2277558435602945:ℤ))) (.branch 200 (.leaf (2491595565253614:ℤ)) (.leaf (2923659738464301:ℤ)))), (.branch 172 (.branch 156 (.leaf (1873342517627084:ℤ)) (.leaf (2288492586813860:ℤ))) (.branch 200 (.leaf (2506290221881032:ℤ)) (.leaf (2947416647566777:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 2 9) 8000 (endpointMeanRuns 2 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 2 9, EndpointRunConditions (endpointMeanCutoff 2 9) (endpointMeanBox 2 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 2 9 h) (endpointMeanCornerA 2 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 9, endpointJoint24Q (endpointMeanCornerK 2 9 h) (endpointMeanCornerA 2 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 2 9, endpointRunWeightQ (endpointMeanCutoff 2 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 2 9) = (452989593/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 2 9 h = (logRoundedQ ((endpointMeanCutoff 2 9:ℚ)/200)).2+(452989593/1000000000000000:ℚ)+((endpointMeanRuns 2 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 2 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 2 9) r*endpointJoint24Q (endpointMeanCornerK 2 9 h) (endpointMeanCornerA 2 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 2 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 2 9 h≤endpointMeanCorner 2 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 2 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint02_09

namespace EndpointAnalyticJoint02_10
private noncomputable def weights : IntegerLookupTree := (.branch 1614 (.leaf (137930459500000:ℤ)) (.branch 3046 (.leaf (6566400500000:ℤ)) (.leaf (540402200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 153 (.leaf (1870783441788376:ℤ)) (.branch 200 (.leaf (2244841038361430:ℤ)) (.leaf (2934618939043199:ℤ)))), (.branch 153 (.leaf (1875720825018474:ℤ)) (.branch 200 (.leaf (2254657739388580:ℤ)) (.leaf (2957177814939120:ℤ)))), (.branch 153 (.leaf (1873342517627084:ℤ)) (.branch 200 (.leaf (2250120499498616:ℤ)) (.leaf (2947416647566777:ℤ)))), (.branch 153 (.leaf (1878543430724811:ℤ)) (.branch 200 (.leaf (2260491227861923:ℤ)) (.leaf (2971366599218868:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 2 10) 8000 (endpointMeanRuns 2 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 2 10, EndpointRunConditions (endpointMeanCutoff 2 10) (endpointMeanBox 2 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 2 10 h) (endpointMeanCornerA 2 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 10, endpointJoint24Q (endpointMeanCornerK 2 10 h) (endpointMeanCornerA 2 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 2 10, endpointRunWeightQ (endpointMeanCutoff 2 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 2 10) = (451966327/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 2 10 h = (logRoundedQ ((endpointMeanCutoff 2 10:ℚ)/200)).2+(451966327/1000000000000000:ℚ)+((endpointMeanRuns 2 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 2 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 2 10) r*endpointJoint24Q (endpointMeanCornerK 2 10 h) (endpointMeanCornerA 2 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 2 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 2 10 h≤endpointMeanCorner 2 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 2 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint02_10

namespace EndpointAnalyticJoint02_11
private noncomputable def weights : IntegerLookupTree := (.branch 1614 (.leaf (134954879800000:ℤ)) (.branch 3046 (.leaf (6542409400000:ℤ)) (.leaf (538818800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 153 (.leaf (1875720825018474:ℤ)) (.branch 200 (.leaf (2254657739388580:ℤ)) (.leaf (2957177814939120:ℤ)))), (.branch 153 (.leaf (1880671239020925:ℤ)) (.branch 200 (.leaf (2264517368898151:ℤ)) (.leaf (2979910104450998:ℤ)))), (.branch 153 (.leaf (1878543430724811:ℤ)) (.branch 200 (.leaf (2260491227861923:ℤ)) (.leaf (2971366599218868:ℤ)))), (.branch 153 (.leaf (1883758782985050:ℤ)) (.branch 200 (.leaf (2270909754557284:ℤ)) (.leaf (2995511162034810:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 2 11) 8000 (endpointMeanRuns 2 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 2 11, EndpointRunConditions (endpointMeanCutoff 2 11) (endpointMeanBox 2 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 2 11 h) (endpointMeanCornerA 2 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 2 11, endpointJoint24Q (endpointMeanCornerK 2 11 h) (endpointMeanCornerA 2 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 2 11, endpointRunWeightQ (endpointMeanCutoff 2 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 2 11) = (225476039/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 2 11 h = (logRoundedQ ((endpointMeanCutoff 2 11:ℚ)/200)).2+(225476039/500000000000000:ℚ)+((endpointMeanRuns 2 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 2 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 2 11) r*endpointJoint24Q (endpointMeanCornerK 2 11 h) (endpointMeanCornerA 2 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 2 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 2 11 h≤endpointMeanCorner 2 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 2 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint02_11

namespace EndpointAnalyticJoint03_00
private noncomputable def weights : IntegerLookupTree := (.branch 1547 (.leaf (170514053500000:ℤ)) (.branch 2975 (.leaf (9073245800000:ℤ)) (.leaf (743156500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 152 (.leaf (1817732830382470:ℤ)) (.branch 200 (.leaf (2147515010903222:ℤ)) (.leaf (2739273359151432:ℤ)))), (.branch 152 (.leaf (1817977783967651:ℤ)) (.branch 200 (.leaf (2147996758868412:ℤ)) (.leaf (2740369889345232:ℤ)))), (.branch 152 (.leaf (1817968960749325:ℤ)) (.branch 200 (.leaf (2147998764791173:ℤ)) (.leaf (2740443223335546:ℤ)))), (.branch 152 (.leaf (1818226233561741:ℤ)) (.branch 200 (.leaf (2148505797670576:ℤ)) (.leaf (2741601123186562:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 3 0) 8000 (endpointMeanRuns 3 0) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 3 0, EndpointRunConditions (endpointMeanCutoff 3 0) (endpointMeanBox 3 0).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 0, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 3 0 h) (endpointMeanCornerA 3 0 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 0, endpointJoint24Q (endpointMeanCornerK 3 0 h) (endpointMeanCornerA 3 0 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 3 0, endpointRunWeightQ (endpointMeanCutoff 3 0) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 3 0) = (462353827/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 3 0 h = (logRoundedQ ((endpointMeanCutoff 3 0:ℚ)/200)).2+(462353827/1000000000000000:ℚ)+((endpointMeanRuns 3 0).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 3 0).map (fun r => endpointRunWeightQ (endpointMeanCutoff 3 0) r*endpointJoint24Q (endpointMeanCornerK 3 0 h) (endpointMeanCornerA 3 0 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 3 0).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 3 0 h≤endpointMeanCorner 3 0 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 3 0 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint03_00

namespace EndpointAnalyticJoint03_01
private noncomputable def weights : IntegerLookupTree := (.branch 1547 (.leaf (168643032500000:ℤ)) (.branch 2975 (.leaf (9055466700000:ℤ)) (.leaf (741989600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 152 (.leaf (1817977783967651:ℤ)) (.branch 200 (.leaf (2147996758868412:ℤ)) (.leaf (2740369889345232:ℤ)))), (.branch 152 (.leaf (1822938120381909:ℤ)) (.branch 200 (.leaf (2157761486510448:ℤ)) (.leaf (2762637432148464:ℤ)))), (.branch 152 (.leaf (1818226233561741:ℤ)) (.branch 200 (.leaf (2148505797670576:ℤ)) (.leaf (2741601123186562:ℤ)))), (.branch 152 (.leaf (1823436409401565:ℤ)) (.branch 200 (.leaf (2158784313446422:ℤ)) (.leaf (2765120466893860:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 3 1) 8000 (endpointMeanRuns 3 1) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 3 1, EndpointRunConditions (endpointMeanCutoff 3 1) (endpointMeanBox 3 1).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 1, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 3 1 h) (endpointMeanCornerA 3 1 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 1, endpointJoint24Q (endpointMeanCornerK 3 1 h) (endpointMeanCornerA 3 1 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 3 1, endpointRunWeightQ (endpointMeanCutoff 3 1) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 3 1) = (461797707/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 3 1 h = (logRoundedQ ((endpointMeanCutoff 3 1:ℚ)/200)).2+(461797707/1000000000000000:ℚ)+((endpointMeanRuns 3 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 3 1).map (fun r => endpointRunWeightQ (endpointMeanCutoff 3 1) r*endpointJoint24Q (endpointMeanCornerK 3 1 h) (endpointMeanCornerA 3 1 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 3 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 3 1 h≤endpointMeanCorner 3 1 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 3 1 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint03_01

namespace EndpointAnalyticJoint03_02
private noncomputable def weights : IntegerLookupTree := (.branch 1547 (.leaf (164965415600000:ℤ)) (.branch 2975 (.leaf (9020164200000:ℤ)) (.leaf (739672600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 152 (.leaf (1822938120381909:ℤ)) (.branch 200 (.leaf (2157761486510448:ℤ)) (.leaf (2762637432148464:ℤ)))), (.branch 152 (.leaf (1827911991030497:ℤ)) (.branch 200 (.leaf (2167570604306026:ℤ)) (.leaf (2785085915292786:ℤ)))), (.branch 152 (.leaf (1823436409401565:ℤ)) (.branch 200 (.leaf (2158784313446422:ℤ)) (.leaf (2765120466893860:ℤ)))), (.branch 152 (.leaf (1828661515139430:ℤ)) (.branch 200 (.leaf (2169112001948108:ℤ)) (.leaf (2788841575738961:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 3 2) 8000 (endpointMeanRuns 3 2) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 3 2, EndpointRunConditions (endpointMeanCutoff 3 2) (endpointMeanBox 3 2).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 2, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 3 2 h) (endpointMeanCornerA 3 2 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 2, endpointJoint24Q (endpointMeanCornerK 3 2 h) (endpointMeanCornerA 3 2 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 3 2, endpointRunWeightQ (endpointMeanCutoff 3 2) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 3 2) = (460693463/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 3 2 h = (logRoundedQ ((endpointMeanCutoff 3 2:ℚ)/200)).2+(460693463/1000000000000000:ℚ)+((endpointMeanRuns 3 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 3 2).map (fun r => endpointRunWeightQ (endpointMeanCutoff 3 2) r*endpointJoint24Q (endpointMeanCornerK 3 2 h) (endpointMeanCornerA 3 2 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 3 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 3 2 h≤endpointMeanCorner 3 2 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 3 2 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint03_02

namespace EndpointAnalyticJoint03_03
private noncomputable def weights : IntegerLookupTree := (.branch 1547 (.leaf (161371904000000:ℤ)) (.branch 2975 (.leaf (8985197100000:ℤ)) (.leaf (737377600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 152 (.leaf (1827911991030497:ℤ)) (.branch 200 (.leaf (2167570604306026:ℤ)) (.leaf (2785085915292786:ℤ)))), (.branch 152 (.leaf (1832899432841461:ℤ)) (.branch 200 (.leaf (2177424314051414:ℤ)) (.leaf (2807716809053002:ℤ)))), (.branch 152 (.leaf (1828661515139430:ℤ)) (.branch 200 (.leaf (2169112001948108:ℤ)) (.leaf (2788841575738961:ℤ)))), (.branch 152 (.leaf (1833901593557359:ℤ)) (.branch 200 (.leaf (2179489098419421:ℤ)) (.leaf (2812766180602257:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 3 3) 8000 (endpointMeanRuns 3 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 3 3, EndpointRunConditions (endpointMeanCutoff 3 3) (endpointMeanBox 3 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 3 3 h) (endpointMeanCornerA 3 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 3, endpointJoint24Q (endpointMeanCornerK 3 3 h) (endpointMeanCornerA 3 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 3 3, endpointRunWeightQ (endpointMeanCutoff 3 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 3 3) = (45959971/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 3 3 h = (logRoundedQ ((endpointMeanCutoff 3 3:ℚ)/200)).2+(45959971/100000000000000:ℚ)+((endpointMeanRuns 3 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 3 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 3 3) r*endpointJoint24Q (endpointMeanCornerK 3 3 h) (endpointMeanCornerA 3 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 3 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 3 3 h≤endpointMeanCorner 3 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 3 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint03_03

namespace EndpointAnalyticJoint03_04
private noncomputable def weights : IntegerLookupTree := (.branch 1547 (.leaf (156995095000000:ℤ)) (.branch 2975 (.leaf (8941950300000:ℤ)) (.leaf (734539200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 152 (.leaf (1832899432841461:ℤ)) (.branch 200 (.leaf (2177424314051414:ℤ)) (.leaf (2807716809053002:ℤ)))), (.branch 152 (.leaf (1837900482843595:ℤ)) (.branch 200 (.leaf (2187322818460270:ℤ)) (.leaf (2830531595650986:ℤ)))), (.branch 152 (.leaf (1833901593557359:ℤ)) (.branch 200 (.leaf (2179489098419421:ℤ)) (.leaf (2812766180602257:ℤ)))), (.branch 152 (.leaf (1839156687559964:ℤ)) (.branch 200 (.leaf (2189915839229560:ℤ)) (.leaf (2836896027212827:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 3 4) 8000 (endpointMeanRuns 3 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 3 4, EndpointRunConditions (endpointMeanCutoff 3 4) (endpointMeanBox 3 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 3 4 h) (endpointMeanCornerA 3 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 4, endpointJoint24Q (endpointMeanCornerK 3 4 h) (endpointMeanCornerA 3 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 3 4, endpointRunWeightQ (endpointMeanCutoff 3 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 3 4) = (458246973/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 3 4 h = (logRoundedQ ((endpointMeanCutoff 3 4:ℚ)/200)).2+(458246973/1000000000000000:ℚ)+((endpointMeanRuns 3 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 3 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 3 4) r*endpointJoint24Q (endpointMeanCornerK 3 4 h) (endpointMeanCornerA 3 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 3 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 3 4 h≤endpointMeanCorner 3 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 3 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint03_04

namespace EndpointAnalyticJoint03_05
private noncomputable def weights : IntegerLookupTree := (.branch 1547 (.leaf (153583236000000:ℤ)) (.branch 2975 (.leaf (8907715100000:ℤ)) (.leaf (732292200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 152 (.leaf (1837900482843595:ℤ)) (.branch 200 (.leaf (2187322818460270:ℤ)) (.leaf (2830531595650986:ℤ)))), (.branch 152 (.leaf (1842915178166733:ℤ)) (.branch 200 (.leaf (2197266321167757:ℤ)) (.leaf (2853531769352765:ℤ)))), (.branch 152 (.leaf (1839156687559964:ℤ)) (.branch 200 (.leaf (2189915839229560:ℤ)) (.leaf (2836896027212827:ℤ)))), (.branch 152 (.leaf (1844426840174801:ℤ)) (.branch 200 (.leaf (2200392461878518:ℤ)) (.leaf (2861232876275806:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 3 5) 8000 (endpointMeanRuns 3 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 3 5, EndpointRunConditions (endpointMeanCutoff 3 5) (endpointMeanBox 3 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 3 5 h) (endpointMeanCornerA 3 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 5, endpointJoint24Q (endpointMeanCornerK 3 5 h) (endpointMeanCornerA 3 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 3 5, endpointRunWeightQ (endpointMeanCutoff 3 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 3 5) = (457176113/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 3 5 h = (logRoundedQ ((endpointMeanCutoff 3 5:ℚ)/200)).2+(457176113/1000000000000000:ℚ)+((endpointMeanRuns 3 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 3 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 3 5) r*endpointJoint24Q (endpointMeanCornerK 3 5 h) (endpointMeanCornerA 3 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 3 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 3 5 h≤endpointMeanCorner 3 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 3 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint03_05

namespace EndpointAnalyticJoint03_06
private noncomputable def weights : IntegerLookupTree := (.branch 1547 (.leaf (150248876500000:ℤ)) (.branch 2813 (.leaf (7713321100000:ℤ)) (.leaf (1162330800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.leaf (1842915178166733:ℤ)) (.branch 200 (.leaf (2233011797343956:ℤ)) (.leaf (2853531769352765:ℤ)))), (.branch 155 (.leaf (1847943556042006:ℤ)) (.branch 200 (.leaf (2243588213751620:ℤ)) (.leaf (2876718836566391:ℤ)))), (.branch 155 (.leaf (1844426840174801:ℤ)) (.branch 200 (.leaf (2236334079784323:ℤ)) (.leaf (2861232876275806:ℤ)))), (.branch 155 (.leaf (1849712094552736:ℤ)) (.branch 200 (.leaf (2247483050801201:ℤ)) (.leaf (2885778503600887:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 3 6) 8000 (endpointMeanRuns 3 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 3 6, EndpointRunConditions (endpointMeanCutoff 3 6) (endpointMeanBox 3 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 3 6 h) (endpointMeanCornerA 3 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 6, endpointJoint24Q (endpointMeanCornerK 3 6 h) (endpointMeanCornerA 3 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 3 6, endpointRunWeightQ (endpointMeanCutoff 3 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 3 6) = (456115123/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 3 6 h = (logRoundedQ ((endpointMeanCutoff 3 6:ℚ)/200)).2+(456115123/1000000000000000:ℚ)+((endpointMeanRuns 3 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 3 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 3 6) r*endpointJoint24Q (endpointMeanCornerK 3 6 h) (endpointMeanCornerA 3 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 3 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 3 6 h≤endpointMeanCorner 3 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 3 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint03_06

namespace EndpointAnalyticJoint03_07
private noncomputable def weights : IntegerLookupTree := (.branch 1842 (.branch 1547 (.leaf (146990105400000:ℤ)) (.leaf (1532040600000:ℤ))) (.branch 2975 (.leaf (3033458400000:ℤ)) (.leaf (727860000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 184 (.branch 152 (.leaf (1847943556042006:ℤ)) (.leaf (2207255026734764:ℤ))) (.branch 200 (.leaf (2631261465648062:ℤ)) (.leaf (2876718836566391:ℤ)))), (.branch 184 (.branch 152 (.leaf (1852985653802142:ℤ)) (.leaf (2217289140652115:ℤ))) (.branch 200 (.leaf (2649163310362751:ℤ)) (.leaf (2900094315940609:ℤ)))), (.branch 184 (.branch 152 (.leaf (1849712094552736:ℤ)) (.leaf (2210919205002503:ℤ))) (.branch 200 (.leaf (2638062469790798:ℤ)) (.leaf (2885778503600887:ℤ)))), (.branch 184 (.branch 152 (.leaf (1855012493968262:ℤ)) (.leaf (2221496308379362:ℤ))) (.branch 200 (.leaf (2656990211094893:ℤ)) (.leaf (2910534700231865:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 3 7) 8000 (endpointMeanRuns 3 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 3 7, EndpointRunConditions (endpointMeanCutoff 3 7) (endpointMeanBox 3 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 3 7 h) (endpointMeanCornerA 3 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 7, endpointJoint24Q (endpointMeanCornerK 3 7 h) (endpointMeanCornerA 3 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 3 7, endpointRunWeightQ (endpointMeanCutoff 3 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 3 7) = (227531911/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 3 7 h = (logRoundedQ ((endpointMeanCutoff 3 7:ℚ)/200)).2+(227531911/500000000000000:ℚ)+((endpointMeanRuns 3 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 3 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 3 7) r*endpointJoint24Q (endpointMeanCornerK 3 7 h) (endpointMeanCornerA 3 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 3 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 3 7 h≤endpointMeanCorner 3 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 3 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint03_07

namespace EndpointAnalyticJoint03_08
private noncomputable def weights : IntegerLookupTree := (.branch 1842 (.branch 1547 (.leaf (143805065800000:ℤ)) (.leaf (1526083200000:ℤ))) (.branch 2975 (.leaf (3022701500000:ℤ)) (.leaf (725674100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 184 (.branch 152 (.leaf (1852985653802142:ℤ)) (.leaf (2217289140652115:ℤ))) (.branch 200 (.leaf (2649163310362751:ℤ)) (.leaf (2900094315940609:ℤ)))), (.branch 184 (.branch 152 (.leaf (1858041508881731:ℤ)) (.leaf (2227368869344780:ℤ))) (.branch 200 (.leaf (2667186950668031:ℤ)) (.leaf (2923659738464301:ℤ)))), (.branch 184 (.branch 152 (.leaf (1855012493968262:ℤ)) (.leaf (2221496308379362:ℤ))) (.branch 200 (.leaf (2656990211094893:ℤ)) (.leaf (2910534700231865:ℤ)))), (.branch 184 (.branch 152 (.leaf (1860328081819899:ℤ)) (.leaf (2232124012934041:ℤ))) (.branch 200 (.leaf (2676053756382022:ℤ)) (.leaf (2935503272577360:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 3 8) 8000 (endpointMeanRuns 3 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 3 8, EndpointRunConditions (endpointMeanCutoff 3 8) (endpointMeanBox 3 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 3 8 h) (endpointMeanCornerA 3 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 8, endpointJoint24Q (endpointMeanCornerK 3 8 h) (endpointMeanCornerA 3 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 3 8, endpointRunWeightQ (endpointMeanCutoff 3 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 3 8) = (113505509/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 3 8 h = (logRoundedQ ((endpointMeanCutoff 3 8:ℚ)/200)).2+(113505509/250000000000000:ℚ)+((endpointMeanRuns 3 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 3 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 3 8) r*endpointJoint24Q (endpointMeanCornerK 3 8 h) (endpointMeanCornerA 3 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 3 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 3 8 h≤endpointMeanCorner 3 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 3 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint03_08

namespace EndpointAnalyticJoint03_09
private noncomputable def weights : IntegerLookupTree := (.branch 2149 (.branch 1547 (.leaf (140691952400000:ℤ)) (.leaf (3273812300000:ℤ))) (.branch 2813 (.leaf (768293100000:ℤ)) (.leaf (1151711600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 172 (.branch 155 (.leaf (1858041508881731:ℤ)) (.leaf (2264891565954226:ℤ))) (.branch 200 (.leaf (2491595565253614:ℤ)) (.leaf (2923659738464301:ℤ)))), (.branch 172 (.branch 155 (.leaf (1863111158817489:ℤ)) (.leaf (2275618977402853:ℤ))) (.branch 200 (.leaf (2506290221881032:ℤ)) (.leaf (2947416647566777:ℤ)))), (.branch 172 (.branch 155 (.leaf (1860328081819899:ℤ)) (.leaf (2269948015440320:ℤ))) (.branch 200 (.leaf (2498669287518788:ℤ)) (.leaf (2935503272577360:ℤ)))), (.branch 172 (.branch 155 (.leaf (1865658901630512:ℤ)) (.leaf (2281264564636947:ℤ))) (.branch 200 (.leaf (2514197513231124:ℤ)) (.leaf (2960686042542597:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 3 9) 8000 (endpointMeanRuns 3 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 3 9, EndpointRunConditions (endpointMeanCutoff 3 9) (endpointMeanBox 3 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 3 9 h) (endpointMeanCornerA 3 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 9, endpointJoint24Q (endpointMeanCornerK 3 9 h) (endpointMeanCornerA 3 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 3 9, endpointRunWeightQ (endpointMeanCutoff 3 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 3 9) = (452989593/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 3 9 h = (logRoundedQ ((endpointMeanCutoff 3 9:ℚ)/200)).2+(452989593/1000000000000000:ℚ)+((endpointMeanRuns 3 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 3 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 3 9) r*endpointJoint24Q (endpointMeanCornerK 3 9 h) (endpointMeanCornerA 3 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 3 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 3 9 h≤endpointMeanCorner 3 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 3 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint03_09

namespace EndpointAnalyticJoint03_10
private noncomputable def weights : IntegerLookupTree := (.branch 2149 (.branch 1547 (.leaf (136899037800000:ℤ)) (.leaf (3258332700000:ℤ))) (.branch 2813 (.leaf (765082000000:ℤ)) (.leaf (1147370600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 172 (.branch 155 (.leaf (1863111158817489:ℤ)) (.leaf (2275618977402853:ℤ))) (.branch 200 (.leaf (2506290221881032:ℤ)) (.leaf (2947416647566777:ℤ)))), (.branch 172 (.branch 155 (.leaf (1868194641248565:ℤ)) (.leaf (2286397198063765:ℤ))) (.branch 200 (.leaf (2521071543028336:ℤ)) (.leaf (2971366599218868:ℤ)))), (.branch 172 (.branch 155 (.leaf (1865658901630512:ℤ)) (.leaf (2281264564636947:ℤ))) (.branch 200 (.leaf (2514197513231124:ℤ)) (.leaf (2960686042542597:ℤ)))), (.branch 172 (.branch 155 (.leaf (1871004997047687:ℤ)) (.leaf (2292637531110460:ℤ))) (.branch 200 (.leaf (2529822240627357:ℤ)) (.leaf (2986084847662367:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 3 10) 8000 (endpointMeanRuns 3 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 3 10, EndpointRunConditions (endpointMeanCutoff 3 10) (endpointMeanBox 3 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 3 10 h) (endpointMeanCornerA 3 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 10, endpointJoint24Q (endpointMeanCornerK 3 10 h) (endpointMeanCornerA 3 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 3 10, endpointRunWeightQ (endpointMeanCutoff 3 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 3 10) = (225855963/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 3 10 h = (logRoundedQ ((endpointMeanCutoff 3 10:ℚ)/200)).2+(225855963/500000000000000:ℚ)+((endpointMeanRuns 3 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 3 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 3 10) r*endpointJoint24Q (endpointMeanCornerK 3 10 h) (endpointMeanCornerA 3 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 3 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 3 10 h≤endpointMeanCorner 3 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 3 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint03_10

namespace EndpointAnalyticJoint03_11
private noncomputable def weights : IntegerLookupTree := (.branch 2149 (.branch 1547 (.leaf (133941415300000:ℤ)) (.leaf (3246071500000:ℤ))) (.branch 2813 (.leaf (762538500000:ℤ)) (.leaf (1143932200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 172 (.branch 155 (.leaf (1868194641248565:ℤ)) (.leaf (2286397198063765:ℤ))) (.branch 200 (.leaf (2521071543028336:ℤ)) (.leaf (2971366599218868:ℤ)))), (.branch 172 (.branch 155 (.leaf (1873291993916801:ℤ)) (.leaf (2297226468589249:ℤ))) (.branch 200 (.leaf (2535940039815932:ℤ)) (.leaf (2995511162034810:ℤ)))), (.branch 172 (.branch 155 (.leaf (1871004997047687:ℤ)) (.leaf (2292637531110460:ℤ))) (.branch 200 (.leaf (2529822240627357:ℤ)) (.leaf (2986084847662367:ℤ)))), (.branch 172 (.branch 155 (.leaf (1876366411844078:ℤ)) (.leaf (2304067196122324:ℤ))) (.branch 200 (.leaf (2545544069426699:ℤ)) (.leaf (3011701541235096:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 3 11) 8000 (endpointMeanRuns 3 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 3 11, EndpointRunConditions (endpointMeanCutoff 3 11) (endpointMeanBox 3 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 3 11 h) (endpointMeanCornerA 3 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 11, endpointJoint24Q (endpointMeanCornerK 3 11 h) (endpointMeanCornerA 3 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 3 11, endpointRunWeightQ (endpointMeanCutoff 3 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 3 11) = (90139981/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 3 11 h = (logRoundedQ ((endpointMeanCutoff 3 11:ℚ)/200)).2+(90139981/200000000000000:ℚ)+((endpointMeanRuns 3 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 3 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 3 11) r*endpointJoint24Q (endpointMeanCornerK 3 11 h) (endpointMeanCornerA 3 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 3 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 3 11 h≤endpointMeanCorner 3 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 3 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint03_11

namespace EndpointAnalyticJoint03_12
private noncomputable def weights : IntegerLookupTree := (.branch 1842 (.branch 1547 (.leaf (131050190400000:ℤ)) (.leaf (1501348800000:ℤ))) (.branch 2975 (.leaf (2978040400000:ℤ)) (.leaf (716598400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 184 (.branch 152 (.leaf (1873291993916801:ℤ)) (.leaf (2257883822426030:ℤ))) (.branch 200 (.leaf (2721996959743577:ℤ)) (.leaf (2995511162034810:ℤ)))), (.branch 184 (.branch 152 (.leaf (1878403254667019:ℤ)) (.leaf (2268148093301825:ℤ))) (.branch 200 (.leaf (2740516125369405:ℤ)) (.leaf (3019851917374995:ℤ)))), (.branch 184 (.branch 152 (.leaf (1876366411844078:ℤ)) (.leaf (2264313160236524:ℤ))) (.branch 200 (.leaf (2734068994898825:ℤ)) (.leaf (3011701541235096:ℤ)))), (.branch 184 (.branch 152 (.leaf (1881743189917782:ℤ)) (.leaf (2275145701886718:ℤ))) (.branch 200 (.leaf (2753685570031373:ℤ)) (.leaf (3037537992458093:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 3 12) 8000 (endpointMeanRuns 3 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 3 12, EndpointRunConditions (endpointMeanCutoff 3 12) (endpointMeanBox 3 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 3 12 h) (endpointMeanCornerA 3 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 3 12, endpointJoint24Q (endpointMeanCornerK 3 12 h) (endpointMeanCornerA 3 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 3 12, endpointRunWeightQ (endpointMeanCutoff 3 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 3 12) = (7026511/15625000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 3 12 h = (logRoundedQ ((endpointMeanCutoff 3 12:ℚ)/200)).2+(7026511/15625000000000:ℚ)+((endpointMeanRuns 3 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 3 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 3 12) r*endpointJoint24Q (endpointMeanCornerK 3 12 h) (endpointMeanCornerA 3 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 3 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 3 12 h≤endpointMeanCorner 3 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 3 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint03_12

namespace EndpointAnalyticJoint04_01
private noncomputable def weights : IntegerLookupTree := (.branch 1485 (.leaf (168276707000000:ℤ)) (.branch 2912 (.leaf (11801826400000:ℤ)) (.leaf (964783500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 151 (.leaf (1809474770715027:ℤ)) (.branch 200 (.leaf (2138454534652964:ℤ)) (.leaf (2743475286238185:ℤ)))), (.branch 151 (.leaf (1814161491239006:ℤ)) (.branch 200 (.leaf (2147734749032334:ℤ)) (.leaf (2765120466893860:ℤ)))), (.branch 151 (.leaf (1809741866590425:ℤ)) (.branch 200 (.leaf (2139007062205743:ℤ)) (.leaf (2744851927063165:ℤ)))), (.branch 151 (.leaf (1814657425528465:ℤ)) (.branch 200 (.leaf (2148762501653752:ℤ)) (.leaf (2767690464366681:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 4 1) 8000 (endpointMeanRuns 4 1) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 4 1, EndpointRunConditions (endpointMeanCutoff 4 1) (endpointMeanBox 4 1).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 1, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 4 1 h) (endpointMeanCornerA 4 1 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 1, endpointJoint24Q (endpointMeanCornerK 4 1 h) (endpointMeanCornerA 4 1 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 4 1, endpointRunWeightQ (endpointMeanCutoff 4 1) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 4 1) = (461797707/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 4 1 h = (logRoundedQ ((endpointMeanCutoff 4 1:ℚ)/200)).2+(461797707/1000000000000000:ℚ)+((endpointMeanRuns 4 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 4 1).map (fun r => endpointRunWeightQ (endpointMeanCutoff 4 1) r*endpointJoint24Q (endpointMeanCornerK 4 1 h) (endpointMeanCornerA 4 1 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 4 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 4 1 h≤endpointMeanCorner 4 1 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 4 1 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint04_01

namespace EndpointAnalyticJoint04_02
private noncomputable def weights : IntegerLookupTree := (.branch 1485 (.leaf (164600622100000:ℤ)) (.branch 2856 (.leaf (11236270400000:ℤ)) (.leaf (1127969700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 152 (.leaf (1814161491239006:ℤ)) (.branch 200 (.leaf (2158784313446422:ℤ)) (.leaf (2765120466893860:ℤ)))), (.branch 152 (.leaf (1819269522037773:ℤ)) (.branch 200 (.leaf (2169112001948108:ℤ)) (.leaf (2788841575738961:ℤ)))), (.branch 152 (.leaf (1814657425528465:ℤ)) (.branch 200 (.leaf (2159833222870034:ℤ)) (.leaf (2767690464366681:ℤ)))), (.branch 152 (.leaf (1820015569013295:ℤ)) (.branch 200 (.leaf (2170693085119621:ℤ)) (.leaf (2792730546047899:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 4 2) 8000 (endpointMeanRuns 4 2) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 4 2, EndpointRunConditions (endpointMeanCutoff 4 2) (endpointMeanBox 4 2).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 2, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 4 2 h) (endpointMeanCornerA 4 2 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 2, endpointJoint24Q (endpointMeanCornerK 4 2 h) (endpointMeanCornerA 4 2 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 4 2, endpointRunWeightQ (endpointMeanCutoff 4 2) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 4 2) = (460693463/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 4 2 h = (logRoundedQ ((endpointMeanCutoff 4 2:ℚ)/200)).2+(460693463/1000000000000000:ℚ)+((endpointMeanRuns 4 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 4 2).map (fun r => endpointRunWeightQ (endpointMeanCutoff 4 2) r*endpointJoint24Q (endpointMeanCornerK 4 2 h) (endpointMeanCornerA 4 2 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 4 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 4 2 h≤endpointMeanCorner 4 2 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 4 2 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint04_02

namespace EndpointAnalyticJoint04_03
private noncomputable def weights : IntegerLookupTree := (.branch 1485 (.leaf (161008628000000:ℤ)) (.branch 2856 (.leaf (11192060900000:ℤ)) (.leaf (1124428200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 152 (.leaf (1819269522037773:ℤ)) (.branch 200 (.leaf (2169112001948108:ℤ)) (.leaf (2788841575738961:ℤ)))), (.branch 152 (.leaf (1824391935226844:ℤ)) (.branch 200 (.leaf (2179489098419421:ℤ)) (.leaf (2812766180602257:ℤ)))), (.branch 152 (.leaf (1820015569013295:ℤ)) (.branch 200 (.leaf (2170693085119621:ℤ)) (.leaf (2792730546047899:ℤ)))), (.branch 152 (.leaf (1825389533501698:ℤ)) (.branch 200 (.leaf (2181607551866826:ℤ)) (.leaf (2817997172459709:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 4 3) 8000 (endpointMeanRuns 4 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 4 3, EndpointRunConditions (endpointMeanCutoff 4 3) (endpointMeanBox 4 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 4 3 h) (endpointMeanCornerA 4 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 3, endpointJoint24Q (endpointMeanCornerK 4 3 h) (endpointMeanCornerA 4 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 4 3, endpointRunWeightQ (endpointMeanCutoff 4 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 4 3) = (45959971/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 4 3 h = (logRoundedQ ((endpointMeanCutoff 4 3:ℚ)/200)).2+(45959971/100000000000000:ℚ)+((endpointMeanRuns 4 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 4 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 4 3) r*endpointJoint24Q (endpointMeanCornerK 4 3 h) (endpointMeanCornerA 4 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 4 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 4 3 h≤endpointMeanCorner 4 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 4 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint04_03

namespace EndpointAnalyticJoint04_04
private noncomputable def weights : IntegerLookupTree := (.branch 1485 (.leaf (156633695700000:ℤ)) (.branch 2856 (.leaf (11137383300000:ℤ)) (.leaf (1120048000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 152 (.leaf (1824391935226844:ℤ)) (.branch 200 (.leaf (2179489098419421:ℤ)) (.leaf (2812766180602257:ℤ)))), (.branch 152 (.leaf (1829528771301888:ℤ)) (.branch 200 (.leaf (2189915839229560:ℤ)) (.leaf (2836896027212827:ℤ)))), (.branch 152 (.leaf (1825389533501698:ℤ)) (.branch 200 (.leaf (2181607551866826:ℤ)) (.leaf (2817997172459709:ℤ)))), (.branch 152 (.leaf (1830779365708383:ℤ)) (.branch 200 (.leaf (2192576897668651:ℤ)) (.leaf (2843492393216619:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 4 4) 8000 (endpointMeanRuns 4 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 4 4, EndpointRunConditions (endpointMeanCutoff 4 4) (endpointMeanBox 4 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 4 4 h) (endpointMeanCornerA 4 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 4, endpointJoint24Q (endpointMeanCornerK 4 4 h) (endpointMeanCornerA 4 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 4 4, endpointRunWeightQ (endpointMeanCutoff 4 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 4 4) = (458246973/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 4 4 h = (logRoundedQ ((endpointMeanCutoff 4 4:ℚ)/200)).2+(458246973/1000000000000000:ℚ)+((endpointMeanRuns 4 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 4 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 4 4) r*endpointJoint24Q (endpointMeanCornerK 4 4 h) (endpointMeanCornerA 4 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 4 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 4 4 h≤endpointMeanCorner 4 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 4 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint04_04

namespace EndpointAnalyticJoint04_05
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.branch 1485 (.leaf (153223322300000:ℤ)) (.leaf (1978787500000:ℤ))) (.branch 2856 (.leaf (3978316900000:ℤ)) (.leaf (1116580600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 184 (.branch 152 (.leaf (1829528771301888:ℤ)) (.leaf (2189915839229560:ℤ))) (.branch 200 (.leaf (2600610536287461:ℤ)) (.leaf (2836896027212827:ℤ)))), (.branch 184 (.branch 152 (.leaf (1834680070872610:ℤ)) (.leaf (2200392461878518:ℤ))) (.branch 200 (.leaf (2619269565035735:ℤ)) (.leaf (2861232876275806:ℤ)))), (.branch 184 (.branch 152 (.leaf (1830779365708383:ℤ)) (.leaf (2192576897668651:ℤ))) (.branch 200 (.leaf (2605558853744752:ℤ)) (.leaf (2843492393216619:ℤ)))), (.branch 184 (.branch 152 (.leaf (1836185112486001:ℤ)) (.leaf (2203601398462591:ℤ))) (.branch 200 (.leaf (2625251287574669:ℤ)) (.leaf (2869218276476606:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 4 5) 8000 (endpointMeanRuns 4 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 4 5, EndpointRunConditions (endpointMeanCutoff 4 5) (endpointMeanBox 4 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 4 5 h) (endpointMeanCornerA 4 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 5, endpointJoint24Q (endpointMeanCornerK 4 5 h) (endpointMeanCornerA 4 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 4 5, endpointRunWeightQ (endpointMeanCutoff 4 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 4 5) = (457176113/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 4 5 h = (logRoundedQ ((endpointMeanCutoff 4 5:ℚ)/200)).2+(457176113/1000000000000000:ℚ)+((endpointMeanRuns 4 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 4 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 4 5) r*endpointJoint24Q (endpointMeanCornerK 4 5 h) (endpointMeanCornerA 4 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 4 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 4 5 h≤endpointMeanCorner 4 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 4 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint04_05

namespace EndpointAnalyticJoint04_06
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.branch 1485 (.leaf (149890434700000:ℤ)) (.leaf (1970876700000:ℤ))) (.branch 2856 (.leaf (3963841400000:ℤ)) (.leaf (1113145100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 184 (.branch 152 (.leaf (1834680070872610:ℤ)) (.leaf (2200392461878518:ℤ))) (.branch 200 (.leaf (2619269565035735:ℤ)) (.leaf (2861232876275806:ℤ)))), (.branch 184 (.branch 152 (.leaf (1839845874663043:ℤ)) (.leaf (2210919205002503:ℤ))) (.branch 200 (.leaf (2638062469790798:ℤ)) (.leaf (2885778503600887:ℤ)))), (.branch 184 (.branch 152 (.leaf (1836185112486001:ℤ)) (.leaf (2203601398462591:ℤ))) (.branch 200 (.leaf (2625251287574669:ℤ)) (.leaf (2869218276476606:ℤ)))), (.branch 184 (.branch 152 (.leaf (1841606820825552:ℤ)) (.leaf (2214681331573581:ℤ))) (.branch 200 (.leaf (2645092553947586:ℤ)) (.leaf (2895176909108838:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 4 6) 8000 (endpointMeanRuns 4 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 4 6, EndpointRunConditions (endpointMeanCutoff 4 6) (endpointMeanBox 4 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 4 6 h) (endpointMeanCornerA 4 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 6, endpointJoint24Q (endpointMeanCornerK 4 6 h) (endpointMeanCornerA 4 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 4 6, endpointRunWeightQ (endpointMeanCutoff 4 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 4 6) = (456115123/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 4 6 h = (logRoundedQ ((endpointMeanCutoff 4 6:ℚ)/200)).2+(456115123/1000000000000000:ℚ)+((endpointMeanRuns 4 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 4 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 4 6) r*endpointJoint24Q (endpointMeanCornerK 4 6 h) (endpointMeanCornerA 4 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 4 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 4 6 h≤endpointMeanCorner 4 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 4 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint04_06

namespace EndpointAnalyticJoint04_07
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.branch 1485 (.leaf (146633122200000:ℤ)) (.leaf (1963038000000:ℤ))) (.branch 2856 (.leaf (3949498000000:ℤ)) (.leaf (1109741000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 184 (.branch 152 (.leaf (1839845874663043:ℤ)) (.leaf (2210919205002503:ℤ))) (.branch 200 (.leaf (2638062469790798:ℤ)) (.leaf (2885778503600887:ℤ)))), (.branch 184 (.branch 152 (.leaf (1845026223511890:ℤ)) (.leaf (2221496308379362:ℤ))) (.branch 200 (.leaf (2656990211094893:ℤ)) (.leaf (2910534700231865:ℤ)))), (.branch 184 (.branch 152 (.leaf (1841606820825552:ℤ)) (.leaf (2214681331573581:ℤ))) (.branch 200 (.leaf (2645092553947586:ℤ)) (.leaf (2895176909108838:ℤ)))), (.branch 184 (.branch 152 (.leaf (1847044537856773:ℤ)) (.leaf (2225816975720984:ℤ))) (.branch 200 (.leaf (2665083777718166:ℤ)) (.leaf (2921370396862985:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 4 7) 8000 (endpointMeanRuns 4 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 4 7, EndpointRunConditions (endpointMeanCutoff 4 7) (endpointMeanBox 4 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 4 7 h) (endpointMeanCornerA 4 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 7, endpointJoint24Q (endpointMeanCornerK 4 7 h) (endpointMeanCornerA 4 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 4 7, endpointRunWeightQ (endpointMeanCutoff 4 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 4 7) = (227531911/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 4 7 h = (logRoundedQ ((endpointMeanCutoff 4 7:ℚ)/200)).2+(227531911/500000000000000:ℚ)+((endpointMeanRuns 4 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 4 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 4 7) r*endpointJoint24Q (endpointMeanCornerK 4 7 h) (endpointMeanCornerA 4 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 4 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 4 7 h≤endpointMeanCorner 4 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 4 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint04_07

namespace EndpointAnalyticJoint04_08
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.branch 1485 (.leaf (142664935100000:ℤ)) (.leaf (1953339400000:ℤ))) (.branch 2856 (.leaf (3931751000000:ℤ)) (.leaf (1105529200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 184 (.branch 152 (.leaf (1845026223511890:ℤ)) (.leaf (2221496308379362:ℤ))) (.branch 200 (.leaf (2656990211094893:ℤ)) (.leaf (2910534700231865:ℤ)))), (.branch 184 (.branch 152 (.leaf (1850221158372837:ℤ)) (.leaf (2232124012934041:ℤ))) (.branch 200 (.leaf (2676053756382022:ℤ)) (.leaf (2935503272577360:ℤ)))), (.branch 184 (.branch 152 (.leaf (1847044537856773:ℤ)) (.leaf (2225816975720984:ℤ))) (.branch 200 (.leaf (2665083777718166:ℤ)) (.leaf (2921370396862985:ℤ)))), (.branch 184 (.branch 152 (.leaf (1852498310848570:ℤ)) (.leaf (2237008611025585:ℤ))) (.branch 200 (.leaf (2685226092242540:ℤ)) (.leaf (2947800864540043:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 4 8) 8000 (endpointMeanRuns 4 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 4 8, EndpointRunConditions (endpointMeanCutoff 4 8) (endpointMeanBox 4 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 4 8 h) (endpointMeanCornerA 4 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 8, endpointJoint24Q (endpointMeanCornerK 4 8 h) (endpointMeanCornerA 4 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 4 8, endpointRunWeightQ (endpointMeanCutoff 4 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 4 8) = (28360191/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 4 8 h = (logRoundedQ ((endpointMeanCutoff 4 8:ℚ)/200)).2+(28360191/62500000000000:ℚ)+((endpointMeanRuns 4 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 4 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 4 8) r*endpointJoint24Q (endpointMeanCornerK 4 8 h) (endpointMeanCornerA 4 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 4 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 4 8 h≤endpointMeanCorner 4 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 4 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint04_08

namespace EndpointAnalyticJoint04_09
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.branch 1485 (.leaf (139570956200000:ℤ)) (.leaf (1945658600000:ℤ))) (.branch 2184 (.leaf (1440970700000:ℤ)) (.branch 2856 (.leaf (808696500000:ℤ)) (.leaf (1102193600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 168 (.branch 152 (.leaf (1850221158372837:ℤ)) (.leaf (2232124012934041:ℤ))) (.branch 184 (.leaf (2442564996787446:ℤ)) (.branch 200 (.leaf (2676053756382022:ℤ)) (.leaf (2935503272577360:ℤ))))), (.branch 168 (.branch 152 (.leaf (1855430720314889:ℤ)) (.leaf (2242802560744090:ℤ))) (.branch 184 (.leaf (2457004726066211:ℤ)) (.branch 200 (.leaf (2695254080027380:ℤ)) (.leaf (2960686042542597:ℤ))))), (.branch 168 (.branch 152 (.leaf (1852498310848570:ℤ)) (.leaf (2237008611025585:ℤ))) (.branch 184 (.leaf (2449314402186346:ℤ)) (.branch 200 (.leaf (2685226092242540:ℤ)) (.leaf (2947800864540043:ℤ))))), (.branch 168 (.branch 152 (.leaf (1857968187209421:ℤ)) (.leaf (2248256519016643:ℤ))) (.branch 184 (.leaf (2464549556406848:ℤ)) (.branch 200 (.leaf (2705520639442598:ℤ)) (.leaf (2974470456164676:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 4 9) 8000 (endpointMeanRuns 4 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 4 9, EndpointRunConditions (endpointMeanCutoff 4 9) (endpointMeanBox 4 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 4 9 h) (endpointMeanCornerA 4 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 9, endpointJoint24Q (endpointMeanCornerK 4 9 h) (endpointMeanCornerA 4 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 4 9, endpointRunWeightQ (endpointMeanCutoff 4 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 4 9) = (226366461/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 4 9 h = (logRoundedQ ((endpointMeanCutoff 4 9:ℚ)/200)).2+(226366461/500000000000000:ℚ)+((endpointMeanRuns 4 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 4 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 4 9) r*endpointJoint24Q (endpointMeanCornerK 4 9 h) (endpointMeanCornerA 4 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 4 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 4 9 h≤endpointMeanCorner 4 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 4 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint04_09

namespace EndpointAnalyticJoint04_10
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.branch 1485 (.leaf (136546704700000:ℤ)) (.leaf (1938045900000:ℤ))) (.branch 2856 (.leaf (3903766500000:ℤ)) (.leaf (1098887700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 184 (.branch 152 (.leaf (1855430720314889:ℤ)) (.leaf (2242802560744090:ℤ))) (.branch 200 (.leaf (2695254080027380:ℤ)) (.leaf (2960686042542597:ℤ)))), (.branch 184 (.branch 152 (.leaf (1860654950522681:ℤ)) (.leaf (2253532195045147:ℤ))) (.branch 200 (.leaf (2714592163397188:ℤ)) (.leaf (2986084847662367:ℤ)))), (.branch 184 (.branch 152 (.leaf (1857968187209421:ℤ)) (.leaf (2248256519016643:ℤ))) (.branch 200 (.leaf (2705520639442598:ℤ)) (.leaf (2974470456164676:ℤ)))), (.branch 184 (.branch 152 (.leaf (1863454214487776:ℤ)) (.leaf (2259560982638982:ℤ))) (.branch 200 (.leaf (2725968569870702:ℤ)) (.leaf (3001381335159154:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 4 10) 8000 (endpointMeanRuns 4 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 4 10, EndpointRunConditions (endpointMeanCutoff 4 10) (endpointMeanBox 4 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 4 10 h) (endpointMeanCornerA 4 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 10, endpointJoint24Q (endpointMeanCornerK 4 10 h) (endpointMeanCornerA 4 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 4 10, endpointRunWeightQ (endpointMeanCutoff 4 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 4 10) = (225855963/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 4 10 h = (logRoundedQ ((endpointMeanCutoff 4 10:ℚ)/200)).2+(225855963/500000000000000:ℚ)+((endpointMeanRuns 4 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 4 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 4 10) r*endpointJoint24Q (endpointMeanCornerK 4 10 h) (endpointMeanCornerA 4 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 4 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 4 10 h≤endpointMeanCorner 4 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 4 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint04_10

namespace EndpointAnalyticJoint04_11
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.branch 1485 (.leaf (132861867700000:ℤ)) (.leaf (1928624000000:ℤ))) (.branch 2856 (.leaf (3886526100000:ℤ)) (.leaf (1094796000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 184 (.branch 152 (.leaf (1860654950522681:ℤ)) (.leaf (2253532195045147:ℤ))) (.branch 200 (.leaf (2714592163397188:ℤ)) (.leaf (2986084847662367:ℤ)))), (.branch 184 (.branch 152 (.leaf (1865893890296813:ℤ)) (.leaf (2264313160236524:ℤ))) (.branch 200 (.leaf (2734068994898825:ℤ)) (.leaf (3011701541235096:ℤ)))), (.branch 184 (.branch 152 (.leaf (1863454214487776:ℤ)) (.leaf (2259560982638982:ℤ))) (.branch 200 (.leaf (2725968569870702:ℤ)) (.leaf (3001381335159154:ℤ)))), (.branch 184 (.branch 152 (.leaf (1868956440372495:ℤ)) (.leaf (2270922286260101:ℤ))) (.branch 200 (.leaf (2746571042774916:ℤ)) (.leaf (3028535684518838:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 4 11) 8000 (endpointMeanRuns 4 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 4 11, EndpointRunConditions (endpointMeanCutoff 4 11) (endpointMeanBox 4 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 4 11 h) (endpointMeanCornerA 4 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 11, endpointJoint24Q (endpointMeanCornerK 4 11 h) (endpointMeanCornerA 4 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 4 11, endpointRunWeightQ (endpointMeanCutoff 4 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 4 11) = (112612071/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 4 11 h = (logRoundedQ ((endpointMeanCutoff 4 11:ℚ)/200)).2+(112612071/250000000000000:ℚ)+((endpointMeanRuns 4 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 4 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 4 11) r*endpointJoint24Q (endpointMeanCornerK 4 11 h) (endpointMeanCornerA 4 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 4 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 4 11 h≤endpointMeanCorner 4 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 4 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint04_11

namespace EndpointAnalyticJoint04_12
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.branch 1485 (.leaf (129988378700000:ℤ)) (.leaf (1921160300000:ℤ))) (.branch 2912 (.leaf (4088633400000:ℤ)) (.leaf (930882500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 184 (.branch 151 (.leaf (1865893890296813:ℤ)) (.leaf (2251242057896124:ℤ))) (.branch 200 (.leaf (2734068994898825:ℤ)) (.leaf (3011701541235096:ℤ)))), (.branch 184 (.branch 151 (.leaf (1871147581054163:ℤ)) (.leaf (2261863272446170:ℤ))) (.branch 200 (.leaf (2753685570031373:ℤ)) (.leaf (3037537992458093:ℤ)))), (.branch 184 (.branch 151 (.leaf (1868956440372495:ℤ)) (.leaf (2257713498507861:ℤ))) (.branch 200 (.leaf (2746571042774916:ℤ)) (.leaf (3028535684518838:ℤ)))), (.branch 184 (.branch 151 (.leaf (1874474912693242:ℤ)) (.leaf (2268907918868216:ℤ))) (.branch 200 (.leaf (2767329226164737:ℤ)) (.leaf (3055935706989266:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 4 12) 8000 (endpointMeanRuns 4 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 4 12, EndpointRunConditions (endpointMeanCutoff 4 12) (endpointMeanBox 4 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 4 12 h) (endpointMeanCornerA 4 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 4 12, endpointJoint24Q (endpointMeanCornerK 4 12 h) (endpointMeanCornerA 4 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 4 12, endpointRunWeightQ (endpointMeanCutoff 4 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 4 12) = (14045227/31250000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 4 12 h = (logRoundedQ ((endpointMeanCutoff 4 12:ℚ)/200)).2+(14045227/31250000000000:ℚ)+((endpointMeanRuns 4 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 4 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 4 12) r*endpointJoint24Q (endpointMeanCornerK 4 12 h) (endpointMeanCornerA 4 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 4 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 4 12 h≤endpointMeanCorner 4 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 4 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint04_12

namespace EndpointAnalyticJoint05_01
private noncomputable def weights : IntegerLookupTree := (.branch 1428 (.leaf (167831403200000:ℤ)) (.branch 2856 (.leaf (15057824600000:ℤ)) (.leaf (1225983900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 150 (.leaf (1801348897032855:ℤ)) (.branch 200 (.leaf (2129641226927781:ℤ)) (.leaf (2748332565178546:ℤ)))), (.branch 150 (.leaf (1805419560045812:ℤ)) (.branch 200 (.leaf (2137750823795273:ℤ)) (.leaf (2767690464366681:ℤ)))), (.branch 150 (.leaf (1801649586008227:ℤ)) (.branch 200 (.leaf (2130269572063285:ℤ)) (.leaf (2749947401064298:ℤ)))), (.branch 150 (.leaf (1805913348452187:ℤ)) (.branch 200 (.leaf (2138784322011830:ℤ)) (.leaf (2770355346494974:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 5 1) 8000 (endpointMeanRuns 5 1) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 5 1, EndpointRunConditions (endpointMeanCutoff 5 1) (endpointMeanBox 5 1).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 1, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 5 1 h) (endpointMeanCornerA 5 1 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 1, endpointJoint24Q (endpointMeanCornerK 5 1 h) (endpointMeanCornerA 5 1 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 5 1, endpointRunWeightQ (endpointMeanCutoff 5 1) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 5 1) = (461797707/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 5 1 h = (logRoundedQ ((endpointMeanCutoff 5 1:ℚ)/200)).2+(461797707/1000000000000000:ℚ)+((endpointMeanRuns 5 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 5 1).map (fun r => endpointRunWeightQ (endpointMeanCutoff 5 1) r*endpointJoint24Q (endpointMeanCornerK 5 1 h) (endpointMeanCornerA 5 1 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 5 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 5 1 h≤endpointMeanCorner 5 1 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 5 1 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint05_01

namespace EndpointAnalyticJoint05_02
private noncomputable def weights : IntegerLookupTree := (.branch 1428 (.leaf (164157213600000:ℤ)) (.branch 2800 (.leaf (14354487900000:ℤ)) (.leaf (1431131200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 151 (.leaf (1805419560045812:ℤ)) (.branch 200 (.leaf (2148762501653752:ℤ)) (.leaf (2767690464366681:ℤ)))), (.branch 151 (.leaf (1810656545848456:ℤ)) (.branch 200 (.leaf (2159416710309534:ℤ)) (.leaf (2792730546047899:ℤ)))), (.branch 151 (.leaf (1805913348452187:ℤ)) (.branch 200 (.leaf (2149817570891657:ℤ)) (.leaf (2770355346494974:ℤ)))), (.branch 151 (.leaf (1811399427747628:ℤ)) (.branch 200 (.leaf (2161007356407601:ℤ)) (.leaf (2796765004917941:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 5 2) 8000 (endpointMeanRuns 5 2) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 5 2, EndpointRunConditions (endpointMeanCutoff 5 2) (endpointMeanBox 5 2).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 2, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 5 2 h) (endpointMeanCornerA 5 2 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 2, endpointJoint24Q (endpointMeanCornerK 5 2 h) (endpointMeanCornerA 5 2 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 5 2, endpointRunWeightQ (endpointMeanCutoff 5 2) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 5 2) = (460693463/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 5 2 h = (logRoundedQ ((endpointMeanCutoff 5 2:ℚ)/200)).2+(460693463/1000000000000000:ℚ)+((endpointMeanRuns 5 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 5 2).map (fun r => endpointRunWeightQ (endpointMeanCutoff 5 2) r*endpointJoint24Q (endpointMeanCornerK 5 2 h) (endpointMeanCornerA 5 2 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 5 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 5 2 h≤endpointMeanCorner 5 2 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 5 2 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint05_02

namespace EndpointAnalyticJoint05_03
private noncomputable def weights : IntegerLookupTree := (.branch 1428 (.leaf (160567096600000:ℤ)) (.branch 2856 (.leaf (14937666600000:ℤ)) (.leaf (1218275000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 150 (.leaf (1810656545848456:ℤ)) (.branch 200 (.leaf (2148202377915443:ℤ)) (.leaf (2792730546047899:ℤ)))), (.branch 150 (.leaf (1815908722591147:ℤ)) (.branch 200 (.leaf (2158705030125396:ℤ)) (.leaf (2817997172459709:ℤ)))), (.branch 150 (.leaf (1811399427747628:ℤ)) (.branch 200 (.leaf (2149760392733081:ℤ)) (.leaf (2796765004917941:ℤ)))), (.branch 150 (.leaf (1816902172884795:ℤ)) (.branch 200 (.leaf (2160792791774692:ℤ)) (.leaf (2823426425288662:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 5 3) 8000 (endpointMeanRuns 5 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 5 3, EndpointRunConditions (endpointMeanCutoff 5 3) (endpointMeanBox 5 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 5 3 h) (endpointMeanCornerA 5 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 3, endpointJoint24Q (endpointMeanCornerK 5 3 h) (endpointMeanCornerA 5 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 5 3, endpointRunWeightQ (endpointMeanCutoff 5 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 5 3) = (45959971/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 5 3 h = (logRoundedQ ((endpointMeanCutoff 5 3:ℚ)/200)).2+(45959971/100000000000000:ℚ)+((endpointMeanRuns 5 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 5 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 5 3) r*endpointJoint24Q (endpointMeanCornerK 5 3 h) (endpointMeanCornerA 5 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 5 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 5 3 h≤endpointMeanCorner 5 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 5 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint05_03

namespace EndpointAnalyticJoint05_04
private noncomputable def weights : IntegerLookupTree := (.branch 1742 (.branch 1428 (.leaf (156194486000000:ℤ)) (.leaf (2889804400000:ℤ))) (.branch 2800 (.leaf (4598641400000:ℤ)) (.leaf (1421023600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 182 (.branch 151 (.leaf (1815908722591147:ℤ)) (.leaf (2170123745725834:ℤ))) (.branch 200 (.leaf (2558500720720704:ℤ)) (.leaf (2817997172459709:ℤ)))), (.branch 182 (.branch 151 (.leaf (1821176134338293:ℤ)) (.leaf (2180883869833565:ℤ))) (.branch 200 (.leaf (2577388787889230:ℤ)) (.leaf (2843492393216619:ℤ)))), (.branch 182 (.branch 151 (.leaf (1816902172884795:ℤ)) (.leaf (2172255384679391:ℤ))) (.branch 200 (.leaf (2562416758021006:ℤ)) (.leaf (2823426425288662:ℤ)))), (.branch 182 (.branch 151 (.leaf (1822421634491879:ℤ)) (.leaf (2183561958860165:ℤ))) (.branch 200 (.leaf (2582320915170198:ℤ)) (.leaf (2850342007641147:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 5 4) 8000 (endpointMeanRuns 5 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 5 4, EndpointRunConditions (endpointMeanCutoff 5 4) (endpointMeanBox 5 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 5 4 h) (endpointMeanCornerA 5 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 4, endpointJoint24Q (endpointMeanCornerK 5 4 h) (endpointMeanCornerA 5 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 5 4, endpointRunWeightQ (endpointMeanCutoff 5 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 5 4) = (458246973/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 5 4 h = (logRoundedQ ((endpointMeanCutoff 5 4:ℚ)/200)).2+(458246973/1000000000000000:ℚ)+((endpointMeanRuns 5 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 5 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 5 4) r*endpointJoint24Q (endpointMeanCornerK 5 4 h) (endpointMeanCornerA 5 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 5 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 5 4 h≤endpointMeanCorner 5 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 5 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint05_04

namespace EndpointAnalyticJoint05_05
private noncomputable def weights : IntegerLookupTree := (.branch 1742 (.branch 1428 (.leaf (152785950600000:ℤ)) (.leaf (2878034500000:ℤ))) (.branch 2800 (.leaf (4581726500000:ℤ)) (.leaf (1416599400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 182 (.branch 151 (.leaf (1821176134338293:ℤ)) (.leaf (2180883869833565:ℤ))) (.branch 200 (.leaf (2577388787889230:ℤ)) (.leaf (2843492393216619:ℤ)))), (.branch 182 (.branch 151 (.leaf (1826458825282112:ℤ)) (.leaf (2191697345862373:ℤ))) (.branch 200 (.leaf (2596416295738182:ℤ)) (.leaf (2869218276476606:ℤ)))), (.branch 182 (.branch 151 (.leaf (1822421634491879:ℤ)) (.leaf (2183561958860165:ℤ))) (.branch 200 (.leaf (2582320915170198:ℤ)) (.leaf (2850342007641147:ℤ)))), (.branch 182 (.branch 151 (.leaf (1827957863350873:ℤ)) (.leaf (2194927383680974:ℤ))) (.branch 200 (.leaf (2602379682404025:ℤ)) (.leaf (2877514174888818:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 5 5) 8000 (endpointMeanRuns 5 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 5 5, EndpointRunConditions (endpointMeanCutoff 5 5) (endpointMeanBox 5 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 5 5 h) (endpointMeanCornerA 5 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 5, endpointJoint24Q (endpointMeanCornerK 5 5 h) (endpointMeanCornerA 5 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 5 5, endpointRunWeightQ (endpointMeanCutoff 5 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 5 5) = (457176113/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 5 5 h = (logRoundedQ ((endpointMeanCutoff 5 5:ℚ)/200)).2+(457176113/1000000000000000:ℚ)+((endpointMeanRuns 5 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 5 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 5 5) r*endpointJoint24Q (endpointMeanCornerK 5 5 h) (endpointMeanCornerA 5 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 5 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 5 5 h≤endpointMeanCorner 5 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 5 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint05_05

namespace EndpointAnalyticJoint05_06
private noncomputable def weights : IntegerLookupTree := (.branch 1742 (.branch 1428 (.leaf (149454884000000:ℤ)) (.leaf (2866373000000:ℤ))) (.branch 2800 (.leaf (4564967600000:ℤ)) (.leaf (1412215900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 182 (.branch 151 (.leaf (1826458825282112:ℤ)) (.leaf (2191697345862373:ℤ))) (.branch 200 (.leaf (2596416295738182:ℤ)) (.leaf (2869218276476606:ℤ)))), (.branch 182 (.branch 151 (.leaf (1831756839743010:ℤ)) (.leaf (2202564438347082:ℤ))) (.branch 200 (.leaf (2615584273684868:ℤ)) (.leaf (2895176909108838:ℤ)))), (.branch 182 (.branch 151 (.leaf (1827957863350873:ℤ)) (.leaf (2194927383680974:ℤ))) (.branch 200 (.leaf (2602379682404025:ℤ)) (.leaf (2877514174888818:ℤ)))), (.branch 182 (.branch 151 (.leaf (1833510910398045:ℤ)) (.leaf (2206351965458986:ℤ))) (.branch 200 (.leaf (2622594260691611:ℤ)) (.leaf (2904945373042581:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 5 6) 8000 (endpointMeanRuns 5 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 5 6, EndpointRunConditions (endpointMeanCutoff 5 6) (endpointMeanBox 5 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 5 6 h) (endpointMeanCornerA 5 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 6, endpointJoint24Q (endpointMeanCornerK 5 6 h) (endpointMeanCornerA 5 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 5 6, endpointRunWeightQ (endpointMeanCutoff 5 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 5 6) = (456115123/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 5 6 h = (logRoundedQ ((endpointMeanCutoff 5 6:ℚ)/200)).2+(456115123/1000000000000000:ℚ)+((endpointMeanRuns 5 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 5 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 5 6) r*endpointJoint24Q (endpointMeanCornerK 5 6 h) (endpointMeanCornerA 5 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 5 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 5 6 h≤endpointMeanCorner 5 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 5 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint05_06

namespace EndpointAnalyticJoint05_07
private noncomputable def weights : IntegerLookupTree := (.branch 1742 (.branch 1428 (.leaf (145397086100000:ℤ)) (.leaf (2851945700000:ℤ))) (.branch 2800 (.leaf (4544233800000:ℤ)) (.leaf (1406792800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 182 (.branch 151 (.leaf (1831756839743010:ℤ)) (.leaf (2202564438347082:ℤ))) (.branch 200 (.leaf (2615584273684868:ℤ)) (.leaf (2895176909108838:ℤ)))), (.branch 182 (.branch 151 (.leaf (1837070222169967:ℤ)) (.leaf (2213485413134148:ℤ))) (.branch 200 (.leaf (2634893758746248:ℤ)) (.leaf (2921370396862985:ℤ)))), (.branch 182 (.branch 151 (.leaf (1833510910398045:ℤ)) (.leaf (2206351965458986:ℤ))) (.branch 200 (.leaf (2622594260691611:ℤ)) (.leaf (2904945373042581:ℤ)))), (.branch 182 (.branch 151 (.leaf (1839080826724384:ℤ)) (.leaf (2217836012105758:ℤ))) (.branch 200 (.leaf (2642965860330890:ℤ)) (.leaf (2932638071431067:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 5 7) 8000 (endpointMeanRuns 5 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 5 7, EndpointRunConditions (endpointMeanCutoff 5 7) (endpointMeanBox 5 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 5 7 h) (endpointMeanCornerA 5 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 7, endpointJoint24Q (endpointMeanCornerK 5 7 h) (endpointMeanCornerA 5 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 5 7, endpointRunWeightQ (endpointMeanCutoff 5 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 5 7) = (45480249/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 5 7 h = (logRoundedQ ((endpointMeanCutoff 5 7:ℚ)/200)).2+(45480249/100000000000000:ℚ)+((endpointMeanRuns 5 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 5 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 5 7) r*endpointJoint24Q (endpointMeanCornerK 5 7 h) (endpointMeanCornerA 5 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 5 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 5 7 h≤endpointMeanCorner 5 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 5 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint05_07

namespace EndpointAnalyticJoint05_08
private noncomputable def weights : IntegerLookupTree := (.branch 1742 (.branch 1428 (.leaf (142233421300000:ℤ)) (.leaf (2840521100000:ℤ))) (.branch 2164 (.leaf (1773382500000:ℤ)) (.branch 2800 (.leaf (913742700000:ℤ)) (.leaf (1402498400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 151 (.leaf (1837070222169967:ℤ)) (.leaf (2213485413134148:ℤ))) (.branch 182 (.leaf (2406949310522483:ℤ)) (.branch 200 (.leaf (2634893758746248:ℤ)) (.leaf (2921370396862985:ℤ))))), (.branch 166 (.branch 151 (.leaf (1842399017140886:ℤ)) (.leaf (2224460537388186:ℤ))) (.branch 182 (.leaf (2421543415337569:ℤ)) (.branch 200 (.leaf (2654345795595042:ℤ)) (.leaf (2947800864540043:ℤ))))), (.branch 166 (.branch 151 (.leaf (1839080826724384:ℤ)) (.leaf (2217836012105758:ℤ))) (.branch 182 (.leaf (2412863496586037:ℤ)) (.branch 200 (.leaf (2642965860330890:ℤ)) (.leaf (2932638071431067:ℤ))))), (.branch 166 (.branch 151 (.leaf (1844667663576099:ℤ)) (.leaf (2229379833135514:ℤ))) (.branch 182 (.leaf (2428238243949765:ℤ)) (.branch 200 (.leaf (2663495701021055:ℤ)) (.leaf (2960594762922886:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 5 8) 8000 (endpointMeanRuns 5 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 5 8, EndpointRunConditions (endpointMeanCutoff 5 8) (endpointMeanBox 5 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 5 8 h) (endpointMeanCornerA 5 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 8, endpointJoint24Q (endpointMeanCornerK 5 8 h) (endpointMeanCornerA 5 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 5 8, endpointRunWeightQ (endpointMeanCutoff 5 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 5 8) = (28360191/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 5 8 h = (logRoundedQ ((endpointMeanCutoff 5 8:ℚ)/200)).2+(28360191/62500000000000:ℚ)+((endpointMeanRuns 5 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 5 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 5 8) r*endpointJoint24Q (endpointMeanCornerK 5 8 h) (endpointMeanCornerA 5 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 5 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 5 8 h≤endpointMeanCorner 5 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 5 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint05_08

namespace EndpointAnalyticJoint05_09
private noncomputable def weights : IntegerLookupTree := (.branch 2131 (.branch 1428 (.leaf (138379117100000:ℤ)) (.branch 1605 (.leaf (1560234000000:ℤ)) (.leaf (3116654900000:ℤ)))) (.branch 2800 (.leaf (1037933400000:ℤ)) (.branch 4080 (.leaf (336970200000:ℤ)) (.leaf (36954500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 167 (.branch 135 (.leaf (1842399017140886:ℤ)) (.branch 151 (.leaf (2034323263955888:ℤ)) (.leaf (2224460537388186:ℤ)))) (.branch 189 (.leaf (2435383212729412:ℤ)) (.branch 200 (.leaf (2764261065954334:ℤ)) (.leaf (2947800864540043:ℤ))))), (.branch 167 (.branch 135 (.leaf (1847743269362973:ℤ)) (.branch 151 (.leaf (2042286960629100:ℤ)) (.leaf (2235490079598481:ℤ)))) (.branch 189 (.leaf (2450340026268922:ℤ)) (.branch 200 (.leaf (2786393676764661:ℤ)) (.leaf (2974470456164676:ℤ))))), (.branch 167 (.branch 135 (.leaf (1844667663576099:ℤ)) (.branch 151 (.leaf (2037793135291445:ℤ)) (.leaf (2229379833135514:ℤ)))) (.branch 189 (.leaf (2442213170462295:ℤ)) (.branch 200 (.leaf (2774704317842961:ℤ)) (.leaf (2960594762922886:ℤ))))), (.branch 167 (.branch 135 (.leaf (1850271472355070:ℤ)) (.branch 151 (.leaf (2046157832458187:ℤ)) (.leaf (2240983739673505:ℤ)))) (.branch 189 (.leaf (2457976663424017:ℤ)) (.branch 200 (.leaf (2798092648828097:ℤ)) (.leaf (2988817964151035:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 5 9) 8000 (endpointMeanRuns 5 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 5 9, EndpointRunConditions (endpointMeanCutoff 5 9) (endpointMeanBox 5 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 5 9 h) (endpointMeanCornerA 5 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 9, endpointJoint24Q (endpointMeanCornerK 5 9 h) (endpointMeanCornerA 5 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 5 9, endpointRunWeightQ (endpointMeanCutoff 5 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 5 9) = (452476823/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 5 9 h = (logRoundedQ ((endpointMeanCutoff 5 9:ℚ)/200)).2+(452476823/1000000000000000:ℚ)+((endpointMeanRuns 5 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 5 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 5 9) r*endpointJoint24Q (endpointMeanCornerK 5 9 h) (endpointMeanCornerA 5 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 5 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 5 9 h≤endpointMeanCorner 5 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 5 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint05_09

namespace EndpointAnalyticJoint05_10
private noncomputable def weights : IntegerLookupTree := (.branch 1742 (.branch 1428 (.leaf (135373779400000:ℤ)) (.leaf (2815186900000:ℤ))) (.branch 2856 (.leaf (4740966300000:ℤ)) (.leaf (1189720200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 182 (.branch 150 (.leaf (1847743269362973:ℤ)) (.leaf (2222808079062985:ℤ))) (.branch 200 (.leaf (2673941436616226:ℤ)) (.leaf (2974470456164676:ℤ)))), (.branch 182 (.branch 150 (.leaf (1853103023673123:ℤ)) (.leaf (2233675481698731:ℤ))) (.branch 200 (.leaf (2693681741963997:ℤ)) (.leaf (3001381335159154:ℤ)))), (.branch 182 (.branch 150 (.leaf (1850271472355070:ℤ)) (.leaf (2228186373081494:ℤ))) (.branch 200 (.leaf (2684185011935599:ℤ)) (.leaf (2988817964151035:ℤ)))), (.branch 182 (.branch 150 (.leaf (1855892304619325:ℤ)) (.leaf (2239621248005238:ℤ))) (.branch 200 (.leaf (2705035031795889:ℤ)) (.leaf (3017310215739451:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 5 10) 8000 (endpointMeanRuns 5 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 5 10, EndpointRunConditions (endpointMeanCutoff 5 10) (endpointMeanBox 5 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 5 10 h) (endpointMeanCornerA 5 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 10, endpointJoint24Q (endpointMeanCornerK 5 10 h) (endpointMeanCornerA 5 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 5 10, endpointRunWeightQ (endpointMeanCutoff 5 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 5 10) = (90291617/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 5 10 h = (logRoundedQ ((endpointMeanCutoff 5 10:ℚ)/200)).2+(90291617/200000000000000:ℚ)+((endpointMeanRuns 5 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 5 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 5 10) r*endpointJoint24Q (endpointMeanCornerK 5 10 h) (endpointMeanCornerA 5 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 5 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 5 10 h≤endpointMeanCorner 5 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 5 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint05_10

namespace EndpointAnalyticJoint05_11
private noncomputable def weights : IntegerLookupTree := (.branch 1742 (.branch 1428 (.leaf (131711979000000:ℤ)) (.leaf (2801328500000:ℤ))) (.branch 2164 (.leaf (1750927100000:ℤ)) (.branch 2856 (.leaf (977903100000:ℤ)) (.leaf (1185298000000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 150 (.leaf (1853103023673123:ℤ)) (.leaf (2233675481698731:ℤ))) (.branch 182 (.leaf (2450997627702871:ℤ)) (.branch 200 (.leaf (2693681741963997:ℤ)) (.leaf (3001381335159154:ℤ))))), (.branch 166 (.branch 150 (.leaf (1858478325038290:ℤ)) (.leaf (2244596015525224:ℤ))) (.branch 182 (.leaf (2465858811577356:ℤ)) (.branch 200 (.leaf (2713567779619095:ℤ)) (.leaf (3028535684518838:ℤ))))), (.branch 166 (.branch 150 (.leaf (1855892304619325:ℤ)) (.leaf (2239621248005238:ℤ))) (.branch 182 (.leaf (2459282266237616:ℤ)) (.branch 200 (.leaf (2705035031795889:ℤ)) (.leaf (3017310215739451:ℤ))))), (.branch 166 (.branch 150 (.leaf (1861530212083527:ℤ)) (.leaf (2251114805795950:ℤ))) (.branch 182 (.leaf (2474952793639185:ℤ)) (.branch 200 (.leaf (2726047008945352:ℤ)) (.leaf (3046074082531708:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 5 11) 8000 (endpointMeanRuns 5 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 5 11, EndpointRunConditions (endpointMeanCutoff 5 11) (endpointMeanBox 5 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 5 11 h) (endpointMeanCornerA 5 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 11, endpointJoint24Q (endpointMeanCornerK 5 11 h) (endpointMeanCornerA 5 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 5 11, endpointRunWeightQ (endpointMeanCutoff 5 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 5 11) = (112549303/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 5 11 h = (logRoundedQ ((endpointMeanCutoff 5 11:ℚ)/200)).2+(112549303/250000000000000:ℚ)+((endpointMeanRuns 5 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 5 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 5 11) r*endpointJoint24Q (endpointMeanCornerK 5 11 h) (endpointMeanCornerA 5 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 5 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 5 11 h≤endpointMeanCorner 5 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 5 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint05_11

namespace EndpointAnalyticJoint05_12
private noncomputable def weights : IntegerLookupTree := (.branch 1605 (.branch 1428 (.leaf (128856449000000:ℤ)) (.leaf (1540087900000:ℤ))) (.branch 2131 (.leaf (3079218900000:ℤ)) (.branch 2800 (.leaf (1026756800000:ℤ)) (.leaf (1383639500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 167 (.branch 151 (.leaf (1858478325038290:ℤ)) (.leaf (2257713498507861:ℤ))) (.branch 189 (.leaf (2480529787589905:ℤ)) (.branch 200 (.leaf (2831191944812806:ℤ)) (.leaf (3028535684518838:ℤ))))), (.branch 167 (.branch 151 (.leaf (1863869218555860:ℤ)) (.leaf (2268907918868216:ℤ))) (.branch 189 (.leaf (2495763867104890:ℤ)) (.branch 200 (.leaf (2853860451132862:ℤ)) (.leaf (3055935706989266:ℤ))))), (.branch 167 (.branch 151 (.leaf (1861530212083527:ℤ)) (.leaf (2264373061880636:ℤ))) (.branch 189 (.leaf (2489809546894501:ℤ)) (.branch 200 (.leaf (2845462402075922:ℤ)) (.leaf (3046074082531708:ℤ))))), (.branch 167 (.branch 151 (.leaf (1867185246619432:ℤ)) (.leaf (2276159107931052:ℤ))) (.branch 189 (.leaf (2505880255112437:ℤ)) (.branch 200 (.leaf (2869447161834848:ℤ)) (.leaf (3075112153821908:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 5 12) 8000 (endpointMeanRuns 5 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 5 12, EndpointRunConditions (endpointMeanCutoff 5 12) (endpointMeanBox 5 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 5 12 h) (endpointMeanCornerA 5 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 12, endpointJoint24Q (endpointMeanCornerK 5 12 h) (endpointMeanCornerA 5 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 5 12, endpointRunWeightQ (endpointMeanCutoff 5 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 5 12) = (449198363/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 5 12 h = (logRoundedQ ((endpointMeanCutoff 5 12:ℚ)/200)).2+(449198363/1000000000000000:ℚ)+((endpointMeanRuns 5 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 5 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 5 12) r*endpointJoint24Q (endpointMeanCornerK 5 12 h) (endpointMeanCornerA 5 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 5 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 5 12 h≤endpointMeanCorner 5 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 5 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint05_12

namespace EndpointAnalyticJoint05_13
private noncomputable def weights : IntegerLookupTree := (.branch 1605 (.branch 1428 (.leaf (125376831100000:ℤ)) (.leaf (1532489600000:ℤ))) (.branch 2131 (.leaf (3065099600000:ℤ)) (.branch 2800 (.leaf (1022541400000:ℤ)) (.leaf (1378530900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 167 (.branch 151 (.leaf (1863869218555860:ℤ)) (.leaf (2268907918868216:ℤ))) (.branch 189 (.leaf (2495763867104890:ℤ)) (.branch 200 (.leaf (2853860451132862:ℤ)) (.leaf (3055935706989266:ℤ))))), (.branch 167 (.branch 151 (.leaf (1869275749454038:ℤ)) (.leaf (2280157844520670:ℤ))) (.branch 189 (.leaf (2511091506140844:ℤ)) (.branch 200 (.leaf (2876710457396695:ℤ)) (.leaf (3083583625244848:ℤ))))), (.branch 167 (.branch 151 (.leaf (1867185246619432:ℤ)) (.leaf (2276159107931052:ℤ))) (.branch 189 (.leaf (2505880255112437:ℤ)) (.branch 200 (.leaf (2869447161834848:ℤ)) (.leaf (3075112153821908:ℤ))))), (.branch 167 (.branch 151 (.leaf (1872857460256375:ℤ)) (.leaf (2288006500269254:ℤ))) (.branch 189 (.leaf (2522054693217240:ℤ)) (.branch 200 (.leaf (2893634092144423:ℤ)) (.leaf (3104427043587754:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 5 13) 8000 (endpointMeanRuns 5 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 5 13, EndpointRunConditions (endpointMeanCutoff 5 13) (endpointMeanBox 5 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 5 13 h) (endpointMeanCornerA 5 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 5 13, endpointJoint24Q (endpointMeanCornerK 5 13 h) (endpointMeanCornerA 5 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 5 13, endpointRunWeightQ (endpointMeanCutoff 5 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 5 13) = (111990467/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 5 13 h = (logRoundedQ ((endpointMeanCutoff 5 13:ℚ)/200)).2+(111990467/250000000000000:ℚ)+((endpointMeanRuns 5 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 5 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 5 13) r*endpointJoint24Q (endpointMeanCornerK 5 13 h) (endpointMeanCornerA 5 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 5 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 5 13 h≤endpointMeanCorner 5 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 5 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint05_13

private theorem activeIndices00 : ∀ai : Fin 42, endpointMeanActive 0 ai → ai∈
    ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow00 (ai : Fin 42) : endpointMeanActive 0 ai →
    EndpointJointNumericalConditions 0 ai := by
  intro hact
  have hi := activeIndices00 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint00_00.conditions
  · exact EndpointAnalyticJoint00_01.conditions
  · exact EndpointAnalyticJoint00_02.conditions
  · exact EndpointAnalyticJoint00_03.conditions
  · exact EndpointAnalyticJoint00_04.conditions
  · exact EndpointAnalyticJoint00_05.conditions
  · exact EndpointAnalyticJoint00_06.conditions
  · exact EndpointAnalyticJoint00_07.conditions
  · exact EndpointAnalyticJoint00_08.conditions
  · exact EndpointAnalyticJoint00_09.conditions
  · exact EndpointAnalyticJoint00_10.conditions

private theorem activeIndices01 : ∀ai : Fin 42, endpointMeanActive 1 ai → ai∈
    ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow01 (ai : Fin 42) : endpointMeanActive 1 ai →
    EndpointJointNumericalConditions 1 ai := by
  intro hact
  have hi := activeIndices01 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint01_00.conditions
  · exact EndpointAnalyticJoint01_01.conditions
  · exact EndpointAnalyticJoint01_02.conditions
  · exact EndpointAnalyticJoint01_03.conditions
  · exact EndpointAnalyticJoint01_04.conditions
  · exact EndpointAnalyticJoint01_05.conditions
  · exact EndpointAnalyticJoint01_06.conditions
  · exact EndpointAnalyticJoint01_07.conditions
  · exact EndpointAnalyticJoint01_08.conditions
  · exact EndpointAnalyticJoint01_09.conditions
  · exact EndpointAnalyticJoint01_10.conditions
  · exact EndpointAnalyticJoint01_11.conditions

private theorem activeIndices02 : ∀ai : Fin 42, endpointMeanActive 2 ai → ai∈
    ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow02 (ai : Fin 42) : endpointMeanActive 2 ai →
    EndpointJointNumericalConditions 2 ai := by
  intro hact
  have hi := activeIndices02 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint02_00.conditions
  · exact EndpointAnalyticJoint02_01.conditions
  · exact EndpointAnalyticJoint02_02.conditions
  · exact EndpointAnalyticJoint02_03.conditions
  · exact EndpointAnalyticJoint02_04.conditions
  · exact EndpointAnalyticJoint02_05.conditions
  · exact EndpointAnalyticJoint02_06.conditions
  · exact EndpointAnalyticJoint02_07.conditions
  · exact EndpointAnalyticJoint02_08.conditions
  · exact EndpointAnalyticJoint02_09.conditions
  · exact EndpointAnalyticJoint02_10.conditions
  · exact EndpointAnalyticJoint02_11.conditions

private theorem activeIndices03 : ∀ai : Fin 42, endpointMeanActive 3 ai → ai∈
    ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow03 (ai : Fin 42) : endpointMeanActive 3 ai →
    EndpointJointNumericalConditions 3 ai := by
  intro hact
  have hi := activeIndices03 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint03_00.conditions
  · exact EndpointAnalyticJoint03_01.conditions
  · exact EndpointAnalyticJoint03_02.conditions
  · exact EndpointAnalyticJoint03_03.conditions
  · exact EndpointAnalyticJoint03_04.conditions
  · exact EndpointAnalyticJoint03_05.conditions
  · exact EndpointAnalyticJoint03_06.conditions
  · exact EndpointAnalyticJoint03_07.conditions
  · exact EndpointAnalyticJoint03_08.conditions
  · exact EndpointAnalyticJoint03_09.conditions
  · exact EndpointAnalyticJoint03_10.conditions
  · exact EndpointAnalyticJoint03_11.conditions
  · exact EndpointAnalyticJoint03_12.conditions

private theorem activeIndices04 : ∀ai : Fin 42, endpointMeanActive 4 ai → ai∈
    ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow04 (ai : Fin 42) : endpointMeanActive 4 ai →
    EndpointJointNumericalConditions 4 ai := by
  intro hact
  have hi := activeIndices04 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint04_01.conditions
  · exact EndpointAnalyticJoint04_02.conditions
  · exact EndpointAnalyticJoint04_03.conditions
  · exact EndpointAnalyticJoint04_04.conditions
  · exact EndpointAnalyticJoint04_05.conditions
  · exact EndpointAnalyticJoint04_06.conditions
  · exact EndpointAnalyticJoint04_07.conditions
  · exact EndpointAnalyticJoint04_08.conditions
  · exact EndpointAnalyticJoint04_09.conditions
  · exact EndpointAnalyticJoint04_10.conditions
  · exact EndpointAnalyticJoint04_11.conditions
  · exact EndpointAnalyticJoint04_12.conditions

private theorem activeIndices05 : ∀ai : Fin 42, endpointMeanActive 5 ai → ai∈
    ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow05 (ai : Fin 42) : endpointMeanActive 5 ai →
    EndpointJointNumericalConditions 5 ai := by
  intro hact
  have hi := activeIndices05 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint05_01.conditions
  · exact EndpointAnalyticJoint05_02.conditions
  · exact EndpointAnalyticJoint05_03.conditions
  · exact EndpointAnalyticJoint05_04.conditions
  · exact EndpointAnalyticJoint05_05.conditions
  · exact EndpointAnalyticJoint05_06.conditions
  · exact EndpointAnalyticJoint05_07.conditions
  · exact EndpointAnalyticJoint05_08.conditions
  · exact EndpointAnalyticJoint05_09.conditions
  · exact EndpointAnalyticJoint05_10.conditions
  · exact EndpointAnalyticJoint05_11.conditions
  · exact EndpointAnalyticJoint05_12.conditions
  · exact EndpointAnalyticJoint05_13.conditions

end SingularValueBounds.KL.Certificates
