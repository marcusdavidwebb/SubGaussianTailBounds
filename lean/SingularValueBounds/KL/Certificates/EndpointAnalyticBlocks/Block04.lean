import SingularValueBounds.KL.Certificates.EndpointAnalyticLogs
import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SingularValueBounds.KL.Certificates

namespace EndpointAnalyticJoint24_06
private noncomputable def weights : IntegerLookupTree := (.branch 1146 (.branch 825 (.leaf (83262742200000:ℤ)) (.leaf (41541745700000:ℤ))) (.branch 1919 (.leaf (44054964200000:ℤ)) (.leaf (23472555100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 172 (.branch 143 (.leaf (1796643578024123:ℤ)) (.leaf (2185917936304438:ℤ))) (.branch 200 (.leaf (2630429616780329:ℤ)) (.leaf (3196110996247641:ℤ)))), (.branch 172 (.branch 143 (.leaf (1799992281388754:ℤ)) (.leaf (2193527624206087:ℤ))) (.branch 200 (.leaf (2645081222031012:ℤ)) (.leaf (3223054690937450:ℤ)))), (.branch 172 (.branch 143 (.leaf (1799067792058553:ℤ)) (.leaf (2192505824899650:ℤ))) (.branch 200 (.leaf (2645575364744603:ℤ)) (.leaf (3230070948888516:ℤ)))), (.branch 172 (.branch 143 (.leaf (1802547010384536:ℤ)) (.leaf (2200481699263391:ℤ))) (.branch 200 (.leaf (2661103258910478:ℤ)) (.leaf (3259086168568555:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 24 6) 8000 (endpointMeanRuns 24 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 24 6, EndpointRunConditions (endpointMeanCutoff 24 6) (endpointMeanBox 24 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 24 6 h) (endpointMeanCornerA 24 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 6, endpointJoint24Q (endpointMeanCornerK 24 6 h) (endpointMeanCornerA 24 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 24 6, endpointRunWeightQ (endpointMeanCutoff 24 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 24 6) = (220985549/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 24 6 h = (logRoundedQ ((endpointMeanCutoff 24 6:ℚ)/200)).2+(220985549/500000000000000:ℚ)+((endpointMeanRuns 24 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 24 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 24 6) r*endpointJoint24Q (endpointMeanCornerK 24 6 h) (endpointMeanCornerA 24 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 24 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 24 6 h≤endpointMeanCorner 24 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 24 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint24_06

namespace EndpointAnalyticJoint24_07
private noncomputable def weights : IntegerLookupTree := (.branch 1146 (.branch 825 (.leaf (80479381900000:ℤ)) (.leaf (41287748200000:ℤ))) (.branch 1919 (.leaf (43834367000000:ℤ)) (.leaf (23378608500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 172 (.branch 143 (.leaf (1799992281388754:ℤ)) (.leaf (2193527624206087:ℤ))) (.branch 200 (.leaf (2645081222031012:ℤ)) (.leaf (3223054690937450:ℤ)))), (.branch 172 (.branch 143 (.leaf (1809733974700244:ℤ)) (.leaf (2215734697206856:ℤ))) (.branch 200 (.leaf (2688012373346200:ℤ)) (.leaf (3302442570610780:ℤ)))), (.branch 172 (.branch 143 (.leaf (1802547010384536:ℤ)) (.leaf (2200481699263391:ℤ))) (.branch 200 (.leaf (2661103258910478:ℤ)) (.leaf (3259086168568555:ℤ)))), (.branch 172 (.branch 143 (.leaf (1812669764039421:ℤ)) (.leaf (2223764487739705:ℤ))) (.branch 200 (.leaf (2706628505956266:ℤ)) (.leaf (3344669273492902:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 24 7) 8000 (endpointMeanRuns 24 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 24 7, EndpointRunConditions (endpointMeanCutoff 24 7) (endpointMeanBox 24 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 24 7 h) (endpointMeanCornerA 24 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 7, endpointJoint24Q (endpointMeanCornerK 24 7 h) (endpointMeanCornerA 24 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 24 7, endpointRunWeightQ (endpointMeanCutoff 24 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 24 7) = (110202367/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 24 7 h = (logRoundedQ ((endpointMeanCutoff 24 7:ℚ)/200)).2+(110202367/250000000000000:ℚ)+((endpointMeanRuns 24 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 24 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 24 7) r*endpointJoint24Q (endpointMeanCornerK 24 7 h) (endpointMeanCornerA 24 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 24 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 24 7 h≤endpointMeanCorner 24 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 24 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint24_07

namespace EndpointAnalyticJoint24_08
private noncomputable def weights : IntegerLookupTree := (.branch 1146 (.branch 825 (.leaf (76715612900000:ℤ)) (.leaf (40936403400000:ℤ))) (.branch 1919 (.leaf (43529223600000:ℤ)) (.leaf (23248655800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 172 (.branch 143 (.leaf (1809733974700244:ℤ)) (.leaf (2215734697206856:ℤ))) (.branch 200 (.leaf (2688012373346200:ℤ)) (.leaf (3302442570610780:ℤ)))), (.branch 172 (.branch 143 (.leaf (1819528390787023:ℤ)) (.leaf (2238166592583160:ℤ))) (.branch 200 (.leaf (2731640321318479:ℤ)) (.leaf (3383785873335652:ℤ)))), (.branch 172 (.branch 143 (.leaf (1812669764039421:ℤ)) (.leaf (2223764487739705:ℤ))) (.branch 200 (.leaf (2706628505956266:ℤ)) (.leaf (3344669273492902:ℤ)))), (.branch 172 (.branch 143 (.leaf (1822849365111303:ℤ)) (.leaf (2247293626021798:ℤ))) (.branch 200 (.leaf (2752932583403181:ℤ)) (.leaf (3432499777678771:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 24 8) 8000 (endpointMeanRuns 24 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 24 8, EndpointRunConditions (endpointMeanCutoff 24 8) (endpointMeanBox 24 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 24 8 h) (endpointMeanCornerA 24 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 8, endpointJoint24Q (endpointMeanCornerK 24 8 h) (endpointMeanCornerA 24 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 24 8, endpointRunWeightQ (endpointMeanCutoff 24 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 24 8) = (439202629/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 24 8 h = (logRoundedQ ((endpointMeanCutoff 24 8:ℚ)/200)).2+(439202629/1000000000000000:ℚ)+((endpointMeanRuns 24 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 24 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 24 8) r*endpointJoint24Q (endpointMeanCornerK 24 8 h) (endpointMeanCornerA 24 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 24 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 24 8 h≤endpointMeanCorner 24 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 24 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint24_08

namespace EndpointAnalyticJoint24_09
private noncomputable def weights : IntegerLookupTree := (.branch 1146 (.branch 825 (.leaf (73101189900000:ℤ)) (.leaf (40589895400000:ℤ))) (.branch 1919 (.leaf (43228280800000:ℤ)) (.branch 3056 (.leaf (8515812600000:ℤ)) (.leaf (1181575100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 143 (.branch 127 (.leaf (1819528390787023:ℤ)) (.leaf (2019875426080320:ℤ))) (.branch 172 (.leaf (2238166592583160:ℤ)) (.branch 200 (.leaf (2731640321318479:ℤ)) (.leaf (3383785873335652:ℤ))))), (.branch 143 (.branch 127 (.leaf (1829375814988713:ℤ)) (.leaf (2035202610726513:ℤ))) (.branch 172 (.leaf (2260825586416156:ℤ)) (.branch 200 (.leaf (2775976375348284:ℤ)) (.leaf (3467132763634482:ℤ))))), (.branch 143 (.branch 127 (.leaf (1822849365111303:ℤ)) (.leaf (2025525894279985:ℤ))) (.branch 172 (.leaf (2247293626021798:ℤ)) (.branch 200 (.leaf (2752932583403181:ℤ)) (.leaf (3432499777678771:ℤ))))), (.branch 143 (.branch 127 (.leaf (1833086132844226:ℤ)) (.leaf (2041529531920475:ℤ))) (.branch 172 (.leaf (2271071720680047:ℤ)) (.branch 200 (.leaf (2800028815216120:ℤ)) (.leaf (3522636697487456:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 24 9) 8000 (endpointMeanRuns 24 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 24 9, EndpointRunConditions (endpointMeanCutoff 24 9) (endpointMeanBox 24 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 24 9 h) (endpointMeanCornerA 24 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 9, endpointJoint24Q (endpointMeanCornerK 24 9 h) (endpointMeanCornerA 24 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 24 9, endpointRunWeightQ (endpointMeanCutoff 24 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 24 9) = (54702239/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 24 9 h = (logRoundedQ ((endpointMeanCutoff 24 9:ℚ)/200)).2+(54702239/125000000000000:ℚ)+((endpointMeanRuns 24 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 24 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 24 9) r*endpointJoint24Q (endpointMeanCornerK 24 9 h) (endpointMeanCornerA 24 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 24 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 24 9 h≤endpointMeanCorner 24 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 24 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint24_09

namespace EndpointAnalyticJoint24_10
private noncomputable def weights : IntegerLookupTree := (.branch 1146 (.branch 825 (.leaf (70117359500000:ℤ)) (.leaf (40296638500000:ℤ))) (.branch 1919 (.leaf (42973586800000:ℤ)) (.branch 3056 (.leaf (8475358500000:ℤ)) (.leaf (1176817700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 143 (.branch 127 (.leaf (1829375814988713:ℤ)) (.leaf (2035202610726513:ℤ))) (.branch 172 (.leaf (2260825586416156:ℤ)) (.branch 200 (.leaf (2775976375348284:ℤ)) (.leaf (3467132763634482:ℤ))))), (.branch 143 (.branch 127 (.leaf (1839276534189204:ℤ)) (.leaf (2050646100856768:ℤ))) (.branch 172 (.leaf (2283713977829842:ℤ)) (.branch 200 (.leaf (2821032028393956:ℤ)) (.leaf (3552532592382297:ℤ))))), (.branch 143 (.branch 127 (.leaf (1833086132844226:ℤ)) (.leaf (2041529531920475:ℤ))) (.branch 172 (.leaf (2271071720680047:ℤ)) (.branch 200 (.leaf (2800028815216120:ℤ)) (.leaf (3522636697487456:ℤ))))), (.branch 143 (.branch 127 (.leaf (1843380388275051:ℤ)) (.leaf (2057659613966564:ℤ))) (.branch 172 (.leaf (2295101405864354:ℤ)) (.branch 200 (.leaf (2847930753301841:ℤ)) (.leaf (3615140599040889:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 24 10) 8000 (endpointMeanRuns 24 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 24 10, EndpointRunConditions (endpointMeanCutoff 24 10) (endpointMeanBox 24 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 24 10 h) (endpointMeanCornerA 24 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 10, endpointJoint24Q (endpointMeanCornerK 24 10 h) (endpointMeanCornerA 24 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 24 10, endpointRunWeightQ (endpointMeanCutoff 24 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 24 10) = (109069183/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 24 10 h = (logRoundedQ ((endpointMeanCutoff 24 10:ℚ)/200)).2+(109069183/250000000000000:ℚ)+((endpointMeanRuns 24 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 24 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 24 10) r*endpointJoint24Q (endpointMeanCornerK 24 10 h) (endpointMeanCornerA 24 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 24 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 24 10 h≤endpointMeanCorner 24 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 24 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint24_10

namespace EndpointAnalyticJoint24_11
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 825 (.leaf (66764352300000:ℤ)) (.branch 1045 (.leaf (27241682600000:ℤ)) (.leaf (32375686800000:ℤ)))) (.branch 1919 (.leaf (12282906300000:ℤ)) (.branch 3056 (.leaf (8428750000000:ℤ)) (.leaf (1171336500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 156 (.branch 127 (.leaf (1839276534189204:ℤ)) (.branch 143 (.leaf (2050646100856768:ℤ)) (.leaf (2283713977829842:ℤ)))) (.branch 179 (.leaf (2503427623818357:ℤ)) (.branch 200 (.leaf (2979971110195412:ℤ)) (.leaf (3552532592382297:ℤ))))), (.branch 156 (.branch 127 (.leaf (1849230836825027:ℤ)) (.branch 143 (.leaf (2066206779018406:ℤ)) (.leaf (2306834089224342:ℤ)))) (.branch 179 (.leaf (2534953932781021:ℤ)) (.branch 200 (.leaf (3033796613158719:ℤ)) (.leaf (3640035926028061:ℤ))))), (.branch 156 (.branch 127 (.leaf (1843380388275051:ℤ)) (.branch 143 (.leaf (2057659613966564:ℤ)) (.leaf (2295101405864354:ℤ)))) (.branch 179 (.leaf (2520185253691898:ℤ)) (.branch 200 (.leaf (3013091991933236:ℤ)) (.leaf (3615140599040889:ℤ))))), (.branch 156 (.branch 127 (.leaf (1853732454243510:ℤ)) (.branch 143 (.leaf (2073917139452849:ℤ)) (.leaf (2319385343595954:ℤ)))) (.branch 179 (.leaf (2553470822513689:ℤ)) (.branch 200 (.leaf (3070599634766558:ℤ)) (.leaf (3710073638918094:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 24 11) 8000 (endpointMeanRuns 24 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 24 11, EndpointRunConditions (endpointMeanCutoff 24 11) (endpointMeanBox 24 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 24 11 h) (endpointMeanCornerA 24 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 11, endpointJoint24Q (endpointMeanCornerK 24 11 h) (endpointMeanCornerA 24 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 24 11, endpointRunWeightQ (endpointMeanCutoff 24 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 24 11) = (169817/390625000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 24 11 h = (logRoundedQ ((endpointMeanCutoff 24 11:ℚ)/200)).2+(169817/390625000000:ℚ)+((endpointMeanRuns 24 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 24 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 24 11) r*endpointJoint24Q (endpointMeanCornerK 24 11 h) (endpointMeanCornerA 24 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 24 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 24 11 h≤endpointMeanCorner 24 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 24 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint24_11

namespace EndpointAnalyticJoint24_12
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 825 (.leaf (63544009700000:ℤ)) (.branch 1045 (.leaf (27009594600000:ℤ)) (.leaf (32140492400000:ℤ)))) (.branch 1919 (.leaf (12206729900000:ℤ)) (.branch 3056 (.leaf (8382758900000:ℤ)) (.leaf (1165928000000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 156 (.branch 127 (.leaf (1849230836825027:ℤ)) (.branch 143 (.leaf (2066206779018406:ℤ)) (.leaf (2306834089224342:ℤ)))) (.branch 179 (.leaf (2534953932781021:ℤ)) (.branch 200 (.leaf (3033796613158719:ℤ)) (.leaf (3640035926028061:ℤ))))), (.branch 156 (.branch 127 (.leaf (1859239012893762:ℤ)) (.branch 143 (.leaf (2081885534455660:ℤ)) (.leaf (2330188266511548:ℤ)))) (.branch 179 (.leaf (2566877260673792:ℤ)) (.branch 200 (.leaf (3088594335201375:ℤ)) (.leaf (3729694576535812:ℤ))))), (.branch 156 (.branch 127 (.leaf (1853732454243510:ℤ)) (.branch 143 (.leaf (2073917139452849:ℤ)) (.leaf (2319385343595954:ℤ)))) (.branch 179 (.leaf (2553470822513689:ℤ)) (.branch 200 (.leaf (3070599634766558:ℤ)) (.leaf (3710073638918094:ℤ))))), (.branch 156 (.branch 127 (.leaf (1864142655402349:ℤ)) (.branch 143 (.leaf (2090303115307283:ℤ)) (.leaf (2343926224062299:ℤ)))) (.branch 179 (.leaf (2587196013418876:ℤ)) (.branch 200 (.leaf (3129204864063585:ℤ)) (.leaf (3807499605920381:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 24 12) 8000 (endpointMeanRuns 24 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 24 12, EndpointRunConditions (endpointMeanCutoff 24 12) (endpointMeanBox 24 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 24 12 h) (endpointMeanCornerA 24 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 12, endpointJoint24Q (endpointMeanCornerK 24 12 h) (endpointMeanCornerA 24 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 24 12, endpointRunWeightQ (endpointMeanCutoff 24 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 24 12) = (216603387/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 24 12 h = (logRoundedQ ((endpointMeanCutoff 24 12:ℚ)/200)).2+(216603387/500000000000000:ℚ)+((endpointMeanRuns 24 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 24 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 24 12) r*endpointJoint24Q (endpointMeanCornerK 24 12 h) (endpointMeanCornerA 24 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 24 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 24 12 h≤endpointMeanCorner 24 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 24 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint24_12

namespace EndpointAnalyticJoint24_13
private noncomputable def weights : IntegerLookupTree := (.branch 1270 (.branch 825 (.leaf (60450982900000:ℤ)) (.branch 1045 (.leaf (26780540600000:ℤ)) (.leaf (17261942000000:ℤ)))) (.branch 1919 (.branch 1474 (.leaf (9589999500000:ℤ)) (.leaf (12131549300000:ℤ))) (.branch 3056 (.leaf (8337369100000:ℤ)) (.leaf (1160590100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 156 (.branch 127 (.leaf (1859239012893762:ℤ)) (.branch 143 (.leaf (2081885534455660:ℤ)) (.leaf (2330188266511548:ℤ)))) (.branch 179 (.branch 165 (.leaf (2566877260673792:ℤ)) (.leaf (2753287106774306:ℤ))) (.branch 200 (.leaf (3088594335201375:ℤ)) (.leaf (3729694576535812:ℤ))))), (.branch 156 (.branch 127 (.leaf (1869301353962468:ℤ)) (.branch 143 (.leaf (2097683263160524:ℤ)) (.leaf (2353778879353131:ℤ)))) (.branch 179 (.branch 165 (.leaf (2599202607258332:ℤ)) (.leaf (2793349233052774:ℤ))) (.branch 200 (.leaf (3144381836957030:ℤ)) (.leaf (3821561632063245:ℤ))))), (.branch 156 (.branch 127 (.leaf (1864142655402349:ℤ)) (.branch 143 (.leaf (2090303115307283:ℤ)) (.leaf (2343926224062299:ℤ)))) (.branch 179 (.branch 165 (.leaf (2587196013418876:ℤ)) (.leaf (2779905424409257:ℤ))) (.branch 200 (.leaf (3129204864063585:ℤ)) (.leaf (3807499605920381:ℤ))))), (.branch 156 (.branch 127 (.leaf (1874611318227505:ℤ)) (.branch 143 (.leaf (2106818556413531:ℤ)) (.leaf (2368726765915108:ℤ)))) (.branch 179 (.branch 165 (.leaf (2621366632754883:ℤ)) (.leaf (2822443003062325:ℤ))) (.branch 200 (.leaf (3188928628275445:ℤ)) (.leaf (3907483963933231:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 24 13) 8000 (endpointMeanRuns 24 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 24 13, EndpointRunConditions (endpointMeanCutoff 24 13) (endpointMeanBox 24 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 24 13 h) (endpointMeanCornerA 24 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 13, endpointJoint24Q (endpointMeanCornerK 24 13 h) (endpointMeanCornerA 24 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 24 13, endpointRunWeightQ (endpointMeanCutoff 24 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 24 13) = (10792549/25000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 24 13 h = (logRoundedQ ((endpointMeanCutoff 24 13:ℚ)/200)).2+(10792549/25000000000000:ℚ)+((endpointMeanRuns 24 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 24 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 24 13) r*endpointJoint24Q (endpointMeanCornerK 24 13 h) (endpointMeanCornerA 24 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 24 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 24 13 h≤endpointMeanCorner 24 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 24 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint24_13

namespace EndpointAnalyticJoint24_14
private noncomputable def weights : IntegerLookupTree := (.branch 1270 (.branch 938 (.branch 825 (.leaf (57480156200000:ℤ)) (.leaf (13417665600000:ℤ))) (.branch 1045 (.leaf (10212463000000:ℤ)) (.leaf (17134443400000:ℤ)))) (.branch 1919 (.branch 1474 (.leaf (9525646400000:ℤ)) (.leaf (12057338800000:ℤ))) (.branch 3056 (.leaf (8292564900000:ℤ)) (.leaf (1155321200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 143 (.branch 127 (.leaf (1869301353962468:ℤ)) (.leaf (2097683263160524:ℤ))) (.branch 156 (.leaf (2353778879353131:ℤ)) (.leaf (2599202607258332:ℤ)))) (.branch 188 (.branch 179 (.leaf (2793349233052774:ℤ)) (.leaf (3144381836957030:ℤ))) (.branch 200 (.leaf (3408816225198704:ℤ)) (.leaf (3821561632063245:ℤ))))), (.branch 165 (.branch 143 (.branch 127 (.leaf (1879418153176188:ℤ)) (.leaf (2113600867923945:ℤ))) (.branch 156 (.leaf (2377608321401028:ℤ)) (.leaf (2631935035259588:ℤ)))) (.branch 188 (.branch 179 (.leaf (2833994289443402:ℤ)) (.leaf (3201176996246941:ℤ))) (.branch 200 (.leaf (3479260362812655:ℤ)) (.leaf (3915691488395978:ℤ))))), (.branch 165 (.branch 143 (.branch 127 (.leaf (1874611318227505:ℤ)) (.leaf (2106818556413531:ℤ))) (.branch 156 (.leaf (2368726765915108:ℤ)) (.leaf (2621366632754883:ℤ)))) (.branch 188 (.branch 179 (.leaf (2822443003062325:ℤ)) (.leaf (3188928628275445:ℤ))) (.branch 200 (.leaf (3467637707797772:ℤ)) (.leaf (3907483963933231:ℤ))))), (.branch 165 (.branch 143 (.branch 127 (.leaf (1885138771028320:ℤ)) (.leaf (2123464485673840:ℤ))) (.branch 156 (.leaf (2393789716571525:ℤ)) (.leaf (2655988563556943:ℤ)))) (.branch 188 (.branch 179 (.leaf (2865631483570459:ℤ)) (.leaf (3249792275673793:ℤ))) (.branch 200 (.leaf (3543625200234663:ℤ)) (.leaf (4010093895913747:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 24 14) 8000 (endpointMeanRuns 24 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 24 14, EndpointRunConditions (endpointMeanCutoff 24 14) (endpointMeanBox 24 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 24 14 h) (endpointMeanCornerA 24 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 14, endpointJoint24Q (endpointMeanCornerK 24 14 h) (endpointMeanCornerA 24 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 24 14, endpointRunWeightQ (endpointMeanCutoff 24 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 24 14) = (107554141/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 24 14 h = (logRoundedQ ((endpointMeanCutoff 24 14:ℚ)/200)).2+(107554141/250000000000000:ℚ)+((endpointMeanRuns 24 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 24 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 24 14) r*endpointJoint24Q (endpointMeanCornerK 24 14 h) (endpointMeanCornerA 24 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 24 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 24 14 h≤endpointMeanCorner 24 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 24 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint24_14

namespace EndpointAnalyticJoint24_15
private noncomputable def weights : IntegerLookupTree := (.branch 1270 (.branch 938 (.branch 825 (.leaf (54626635700000:ℤ)) (.leaf (13301516900000:ℤ))) (.branch 1045 (.leaf (10130686900000:ℤ)) (.branch 1146 (.leaf (7723754100000:ℤ)) (.leaf (7659595500000:ℤ))))) (.branch 1919 (.branch 1474 (.leaf (9462113100000:ℤ)) (.leaf (11984073700000:ℤ))) (.branch 2357 (.leaf (4106884500000:ℤ)) (.branch 3056 (.leaf (2011171900000:ℤ)) (.leaf (1150119300000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 135 (.branch 127 (.leaf (1879418153176188:ℤ)) (.leaf (2113600867923945:ℤ))) (.branch 143 (.leaf (2239607165486249:ℤ)) (.branch 156 (.leaf (2377608321401028:ℤ)) (.leaf (2631935035259588:ℤ))))) (.branch 179 (.branch 172 (.leaf (2833994289443402:ℤ)) (.leaf (3008687082627217:ℤ))) (.branch 188 (.leaf (3201176996246941:ℤ)) (.branch 200 (.leaf (3479260362812655:ℤ)) (.leaf (3915691488395978:ℤ)))))), (.branch 165 (.branch 135 (.branch 127 (.leaf (1889589705266492:ℤ)) (.leaf (2129639258387408:ℤ))) (.branch 143 (.leaf (2259297316719316:ℤ)) (.branch 156 (.leaf (2401679010540265:ℤ)) (.leaf (2665079671158708:ℤ))))) (.branch 179 (.branch 172 (.leaf (2875230757960181:ℤ)) (.leaf (3057519760931565:ℤ))) (.branch 188 (.leaf (3258998013809175:ℤ)) (.branch 200 (.leaf (3551160248169029:ℤ)) (.leaf (4012139881156033:ℤ)))))), (.branch 165 (.branch 135 (.branch 127 (.leaf (1885138771028320:ℤ)) (.leaf (2123464485673840:ℤ))) (.branch 143 (.leaf (2252259389370479:ℤ)) (.branch 156 (.leaf (2393789716571525:ℤ)) (.leaf (2655988563556943:ℤ))))) (.branch 179 (.branch 172 (.leaf (2865631483570459:ℤ)) (.leaf (3047874804724075:ℤ))) (.branch 188 (.leaf (3249792275673793:ℤ)) (.branch 200 (.leaf (3543625200234663:ℤ)) (.leaf (4010093895913747:ℤ)))))), (.branch 165 (.branch 135 (.branch 127 (.leaf (1895725343957874:ℤ)) (.leaf (2140241934072371:ℤ))) (.branch 143 (.leaf (2272914232804425:ℤ)) (.branch 156 (.leaf (2419117852518471:ℤ)) (.leaf (2691067766561028:ℤ))))) (.branch 179 (.branch 172 (.leaf (2909480825908786:ℤ)) (.leaf (3100016807476161:ℤ))) (.branch 188 (.leaf (3311817561981772:ℤ)) (.branch 200 (.leaf (3621277831735492:ℤ)) (.leaf (4115398349033256:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 24 15) 8000 (endpointMeanRuns 24 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 24 15, EndpointRunConditions (endpointMeanCutoff 24 15) (endpointMeanBox 24 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 24 15 h) (endpointMeanCornerA 24 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 15, endpointJoint24Q (endpointMeanCornerK 24 15 h) (endpointMeanCornerA 24 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 24 15, endpointRunWeightQ (endpointMeanCutoff 24 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 24 15) = (428750091/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 24 15 h = (logRoundedQ ((endpointMeanCutoff 24 15:ℚ)/200)).2+(428750091/1000000000000000:ℚ)+((endpointMeanRuns 24 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 24 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 24 15) r*endpointJoint24Q (endpointMeanCornerK 24 15 h) (endpointMeanCornerA 24 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 24 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 24 15 h≤endpointMeanCorner 24 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 24 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint24_15

namespace EndpointAnalyticJoint24_16
private noncomputable def weights : IntegerLookupTree := (.branch 1270 (.branch 887 (.branch 825 (.leaf (52270572200000:ℤ)) (.leaf (7154768300000:ℤ))) (.branch 983 (.leaf (9945226500000:ℤ)) (.branch 1146 (.leaf (14029327200000:ℤ)) (.leaf (7613047800000:ℤ))))) (.branch 1919 (.branch 1474 (.leaf (9408292800000:ℤ)) (.branch 1618 (.leaf (4298764300000:ℤ)) (.leaf (6073610800000:ℤ)))) (.branch 2357 (.leaf (4087826500000:ℤ)) (.branch 3056 (.leaf (2002627400000:ℤ)) (.leaf (1145712700000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 156 (.branch 135 (.branch 127 (.leaf (1889589705266492:ℤ)) (.leaf (2129639258387408:ℤ))) (.branch 143 (.leaf (2259297316719316:ℤ)) (.branch 151 (.leaf (2401679010540265:ℤ)) (.leaf (2558627137548027:ℤ))))) (.branch 184 (.branch 165 (.leaf (2665079671158708:ℤ)) (.branch 172 (.leaf (2875230757960181:ℤ)) (.leaf (3057519760931565:ℤ)))) (.branch 193 (.leaf (3416304999079301:ℤ)) (.branch 200 (.leaf (3732227835348596:ℤ)) (.leaf (4012139881156033:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1899816306560057:ℤ)) (.leaf (2145799351094920:ℤ))) (.branch 143 (.leaf (2279160579586226:ℤ)) (.branch 151 (.leaf (2425993389134338:ℤ)) (.leaf (2588297355316987:ℤ))))) (.branch 184 (.branch 165 (.leaf (2698641705995932:ℤ)) (.branch 172 (.leaf (2917067244035944:ℤ)) (.leaf (3107145020984994:ℤ)))) (.branch 193 (.leaf (3482827729292029:ℤ)) (.branch 200 (.leaf (3815247977926652:ℤ)) (.leaf (4110963918803730:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1895725343957874:ℤ)) (.leaf (2140241934072371:ℤ))) (.branch 143 (.leaf (2272914232804425:ℤ)) (.branch 151 (.leaf (2419117852518471:ℤ)) (.leaf (2580923466569847:ℤ))))) (.branch 184 (.branch 165 (.leaf (2691067766561028:ℤ)) (.branch 172 (.leaf (2909480825908786:ℤ)) (.leaf (3100016807476161:ℤ)))) (.branch 193 (.leaf (3478089815421974:ℤ)) (.branch 200 (.leaf (3814492580894659:ℤ)) (.leaf (4115398349033256:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1906371369023326:ℤ)) (.leaf (2157151940739084:ℤ))) (.branch 143 (.leaf (2293758496053559:ℤ)) (.branch 151 (.leaf (2444713979620243:ℤ)) (.leaf (2612268424178449:ℤ))))) (.branch 184 (.branch 165 (.leaf (2726610281230037:ℤ)) (.branch 172 (.leaf (2954001142458042:ℤ)) (.leaf (3153050837829506:ℤ)))) (.branch 193 (.leaf (3549789982705680:ℤ)) (.branch 200 (.leaf (3904659672128263:ℤ)) (.leaf (4223468081005230:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 24 16) 8000 (endpointMeanRuns 24 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 24 16, EndpointRunConditions (endpointMeanCutoff 24 16) (endpointMeanBox 24 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 24 16 h) (endpointMeanCornerA 24 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 16, endpointJoint24Q (endpointMeanCornerK 24 16 h) (endpointMeanCornerA 24 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 24 16, endpointRunWeightQ (endpointMeanCutoff 24 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 24 16) = (427507813/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 24 16 h = (logRoundedQ ((endpointMeanCutoff 24 16:ℚ)/200)).2+(427507813/1000000000000000:ℚ)+((endpointMeanRuns 24 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 24 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 24 16) r*endpointJoint24Q (endpointMeanCornerK 24 16 h) (endpointMeanCornerA 24 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 24 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 24 16 h≤endpointMeanCorner 24 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 24 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint24_16

namespace EndpointAnalyticJoint24_17
private noncomputable def weights : IntegerLookupTree := (.branch 1270 (.branch 887 (.branch 825 (.leaf (49622634800000:ℤ)) (.leaf (7092203000000:ℤ))) (.branch 983 (.leaf (9863221100000:ℤ)) (.branch 1146 (.leaf (13922436000000:ℤ)) (.leaf (7559369500000:ℤ))))) (.branch 1919 (.branch 1474 (.leaf (9346227900000:ℤ)) (.branch 1618 (.leaf (4272176600000:ℤ)) (.leaf (6038207200000:ℤ)))) (.branch 2357 (.leaf (4065849000000:ℤ)) (.branch 3056 (.leaf (1992774000000:ℤ)) (.leaf (1140631100000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 156 (.branch 135 (.branch 127 (.leaf (1899816306560057:ℤ)) (.leaf (2145799351094920:ℤ))) (.branch 143 (.leaf (2279160579586226:ℤ)) (.branch 151 (.leaf (2425993389134338:ℤ)) (.leaf (2588297355316987:ℤ))))) (.branch 184 (.branch 165 (.leaf (2698641705995932:ℤ)) (.branch 172 (.leaf (2917067244035944:ℤ)) (.leaf (3107145020984994:ℤ)))) (.branch 193 (.leaf (3482827729292029:ℤ)) (.branch 200 (.leaf (3815247977926652:ℤ)) (.leaf (4110963918803730:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1910098254987301:ℤ)) (.leaf (2162082069545403:ℤ))) (.branch 143 (.leaf (2299198476047744:ℤ)) (.branch 151 (.leaf (2450553924272981:ℤ)) (.leaf (2618311633308533:ℤ))))) (.branch 184 (.branch 165 (.leaf (2732626396183613:ℤ)) (.branch 172 (.leaf (2959512478318203:ℤ)) (.leaf (3157575726833680:ℤ)))) (.branch 193 (.leaf (3550645798660985:ℤ)) (.branch 200 (.leaf (3900114830935512:ℤ)) (.leaf (4212222116452400:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1906371369023326:ℤ)) (.leaf (2157151940739084:ℤ))) (.branch 143 (.leaf (2293758496053559:ℤ)) (.branch 151 (.leaf (2444713979620243:ℤ)) (.leaf (2612268424178449:ℤ))))) (.branch 184 (.branch 165 (.leaf (2726610281230037:ℤ)) (.branch 172 (.leaf (2954001142458042:ℤ)) (.leaf (3153050837829506:ℤ)))) (.branch 193 (.leaf (3549789982705680:ℤ)) (.branch 200 (.leaf (3904659672128263:ℤ)) (.leaf (4223468081005230:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1917077180096308:ℤ)) (.leaf (2174195553014077:ℤ))) (.branch 143 (.leaf (2314793916234229:ℤ)) (.branch 151 (.leaf (2470580933429327:ℤ)) (.leaf (2643994061950646:ℤ))))) (.branch 184 (.branch 165 (.leaf (2762622226793611:ℤ)) (.branch 172 (.leaf (2999202700336676:ℤ)) (.leaf (3206992156288105:ℤ)))) (.branch 193 (.leaf (3622968235450467:ℤ)) (.branch 200 (.leaf (3996958135797146:ℤ)) (.leaf (4334375707629917:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 24 17) 8000 (endpointMeanRuns 24 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 24 17, EndpointRunConditions (endpointMeanCutoff 24 17) (endpointMeanBox 24 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 24 17 h) (endpointMeanCornerA 24 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 17, endpointJoint24Q (endpointMeanCornerK 24 17 h) (endpointMeanCornerA 24 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 24 17, endpointRunWeightQ (endpointMeanCutoff 24 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 24 17) = (13314851/31250000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 24 17 h = (logRoundedQ ((endpointMeanCutoff 24 17:ℚ)/200)).2+(13314851/31250000000000:ℚ)+((endpointMeanRuns 24 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 24 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 24 17) r*endpointJoint24Q (endpointMeanCornerK 24 17 h) (endpointMeanCornerA 24 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 24 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 24 17 h≤endpointMeanCorner 24 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 24 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint24_17

namespace EndpointAnalyticJoint24_18
private noncomputable def weights : IntegerLookupTree := (.branch 1270 (.branch 887 (.branch 825 (.leaf (47079149200000:ℤ)) (.leaf (7030406700000:ℤ))) (.branch 983 (.leaf (9782223600000:ℤ)) (.branch 1146 (.leaf (13816858700000:ℤ)) (.leaf (7506351000000:ℤ))))) (.branch 1919 (.branch 1474 (.leaf (9284925800000:ℤ)) (.branch 1618 (.leaf (4245915800000:ℤ)) (.leaf (6003238800000:ℤ)))) (.branch 2357 (.leaf (4044141700000:ℤ)) (.branch 3056 (.leaf (1983041700000:ℤ)) (.leaf (1135611900000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 156 (.branch 135 (.branch 127 (.leaf (1910098254987301:ℤ)) (.leaf (2162082069545403:ℤ))) (.branch 143 (.leaf (2299198476047744:ℤ)) (.branch 151 (.leaf (2450553924272981:ℤ)) (.leaf (2618311633308533:ℤ))))) (.branch 184 (.branch 165 (.leaf (2732626396183613:ℤ)) (.branch 172 (.leaf (2959512478318203:ℤ)) (.leaf (3157575726833680:ℤ)))) (.branch 193 (.leaf (3550645798660985:ℤ)) (.branch 200 (.leaf (3900114830935512:ℤ)) (.leaf (4212222116452400:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1920435850091067:ℤ)) (.leaf (2178488344245450:ℤ))) (.branch 143 (.leaf (2319412541445411:ℤ)) (.branch 151 (.leaf (2475363108022541:ℤ)) (.leaf (2648673961295764:ℤ))))) (.branch 184 (.branch 165 (.leaf (2767039064329465:ℤ)) (.branch 172 (.leaf (3002575318491091:ℤ)) (.leaf (3208824951314493:ℤ)))) (.branch 193 (.leaf (3619784430196790:ℤ)) (.branch 200 (.leaf (3986869472832881:ℤ)) (.leaf (4315974430515991:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1917077180096308:ℤ)) (.leaf (2174195553014077:ℤ))) (.branch 143 (.leaf (2314793916234229:ℤ)) (.branch 151 (.leaf (2470580933429327:ℤ)) (.leaf (2643994061950646:ℤ))))) (.branch 184 (.branch 165 (.leaf (2762622226793611:ℤ)) (.branch 172 (.leaf (2999202700336676:ℤ)) (.leaf (3206992156288105:ℤ)))) (.branch 193 (.leaf (3622968235450467:ℤ)) (.branch 200 (.leaf (3996958135797146:ℤ)) (.leaf (4334375707629917:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1927843112923422:ℤ)) (.leaf (2191373826512464:ℤ))) (.branch 143 (.leaf (2336022246393409:ℤ)) (.branch 151 (.leaf (2496721579500550:ℤ)) (.leaf (2676105003194240:ℤ))))) (.branch 184 (.branch 165 (.leaf (2799109803301662:ℤ)) (.branch 172 (.leaf (3045095923768617:ℤ)) (.leaf (3261856284427457:ℤ)))) (.branch 193 (.leaf (3697655044110072:ℤ)) (.branch 200 (.leaf (4091438353347542:ℤ)) (.leaf (4448195751587375:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 24 18) 8000 (endpointMeanRuns 24 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 24 18, EndpointRunConditions (endpointMeanCutoff 24 18) (endpointMeanBox 24 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 24 18 h) (endpointMeanCornerA 24 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 18, endpointJoint24Q (endpointMeanCornerK 24 18 h) (endpointMeanCornerA 24 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 24 18, endpointRunWeightQ (endpointMeanCutoff 24 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 24 18) = (21233013/50000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 24 18 h = (logRoundedQ ((endpointMeanCutoff 24 18:ℚ)/200)).2+(21233013/50000000000000:ℚ)+((endpointMeanRuns 24 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 24 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 24 18) r*endpointJoint24Q (endpointMeanCornerK 24 18 h) (endpointMeanCornerA 24 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 24 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 24 18 h≤endpointMeanCorner 24 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 24 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint24_18

namespace EndpointAnalyticJoint24_19
private noncomputable def weights : IntegerLookupTree := (.branch 1270 (.branch 887 (.branch 825 (.leaf (44635980900000:ℤ)) (.leaf (6969360900000:ℤ))) (.branch 983 (.leaf (9702209700000:ℤ)) (.branch 1146 (.leaf (13712563300000:ℤ)) (.leaf (7453976200000:ℤ))))) (.branch 1919 (.branch 1474 (.leaf (9224368100000:ℤ)) (.branch 1618 (.leaf (4219973900000:ℤ)) (.leaf (5968695000000:ℤ)))) (.branch 2357 (.leaf (4022698000000:ℤ)) (.branch 3056 (.leaf (1973427600000:ℤ)) (.leaf (1130653700000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 156 (.branch 135 (.branch 127 (.leaf (1920435850091067:ℤ)) (.leaf (2178488344245450:ℤ))) (.branch 143 (.leaf (2319412541445411:ℤ)) (.branch 151 (.leaf (2475363108022541:ℤ)) (.leaf (2648673961295764:ℤ))))) (.branch 184 (.branch 165 (.leaf (2767039064329465:ℤ)) (.branch 172 (.leaf (3002575318491091:ℤ)) (.leaf (3208824951314493:ℤ)))) (.branch 193 (.leaf (3619784430196790:ℤ)) (.branch 200 (.leaf (3986869472832881:ℤ)) (.leaf (4315974430515991:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1930829393035343:ℤ)) (.leaf (2195019112762512:ℤ))) (.branch 143 (.leaf (2339804324619142:ℤ)) (.branch 151 (.leaf (2500423457678808:ℤ)) (.leaf (2679388375317782:ℤ))))) (.branch 184 (.branch 165 (.leaf (2801885100070158:ℤ)) (.branch 172 (.leaf (3046264751123832:ℤ)) (.leaf (3260905979443775:ℤ)))) (.branch 193 (.leaf (3690269338055745:ℤ)) (.branch 200 (.leaf (4075553895830804:ℤ)) (.leaf (4422282294210148:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1927843112923422:ℤ)) (.leaf (2191373826512464:ℤ))) (.branch 143 (.leaf (2336022246393409:ℤ)) (.branch 151 (.leaf (2496721579500550:ℤ)) (.leaf (2676105003194240:ℤ))))) (.branch 184 (.branch 165 (.leaf (2799109803301662:ℤ)) (.branch 172 (.leaf (3045095923768617:ℤ)) (.leaf (3261856284427457:ℤ)))) (.branch 193 (.leaf (3697655044110072:ℤ)) (.branch 200 (.leaf (4091438353347542:ℤ)) (.leaf (4448195751587375:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1938669505136753:ℤ)) (.leaf (2208687825189742:ℤ))) (.branch 143 (.leaf (2357445255654768:ℤ)) (.branch 151 (.leaf (2523138813708506:ℤ)) (.leaf (2708605927366461:ℤ))))) (.branch 184 (.branch 165 (.leaf (2836079292691798:ℤ)) (.branch 172 (.leaf (3091691396487248:ℤ)) (.leaf (3317659009360881:ℤ)))) (.branch 193 (.leaf (3773881507280913:ℤ)) (.branch 200 (.leaf (4188151897143825:ℤ)) (.leaf (4565004692511858:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 24 19) 8000 (endpointMeanRuns 24 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 24 19, EndpointRunConditions (endpointMeanCutoff 24 19) (endpointMeanBox 24 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 24 19 h) (endpointMeanCornerA 24 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 19, endpointJoint24Q (endpointMeanCornerK 24 19 h) (endpointMeanCornerA 24 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 24 19, endpointRunWeightQ (endpointMeanCutoff 24 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 24 19) = (42326247/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 24 19 h = (logRoundedQ ((endpointMeanCutoff 24 19:ℚ)/200)).2+(42326247/100000000000000:ℚ)+((endpointMeanRuns 24 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 24 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 24 19) r*endpointJoint24Q (endpointMeanCornerK 24 19 h) (endpointMeanCornerA 24 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 24 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 24 19 h≤endpointMeanCorner 24 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 24 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint24_19

namespace EndpointAnalyticJoint24_20
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 983 (.branch 825 (.leaf (42289169800000:ℤ)) (.leaf (17994582700000:ℤ))) (.branch 1146 (.leaf (13609519200000:ℤ)) (.branch 1270 (.leaf (7402229800000:ℤ)) (.leaf (9164536900000:ℤ))))) (.branch 1919 (.branch 1618 (.leaf (4194343200000:ℤ)) (.leaf (5934565600000:ℤ))) (.branch 2357 (.leaf (4001511500000:ℤ)) (.branch 3056 (.leaf (1963928800000:ℤ)) (.leaf (1125755000000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 156 (.branch 135 (.branch 127 (.leaf (1930829393035343:ℤ)) (.leaf (2195019112762512:ℤ))) (.branch 143 (.leaf (2339804324619142:ℤ)) (.branch 151 (.leaf (2500423457678808:ℤ)) (.leaf (2679388375317782:ℤ))))) (.branch 172 (.branch 165 (.leaf (2801885100070158:ℤ)) (.leaf (3046264751123832:ℤ))) (.branch 184 (.leaf (3260905979443775:ℤ)) (.branch 200 (.leaf (3690269338055745:ℤ)) (.leaf (4422282294210148:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1941279186614041:ℤ)) (.leaf (2211675319778464:ℤ))) (.branch 143 (.leaf (2360375388025940:ℤ)) (.branch 151 (.leaf (2525737516022442:ℤ)) (.leaf (2710458958216186:ℤ))))) (.branch 172 (.branch 165 (.leaf (2837169960915450:ℤ)) (.leaf (3090589893546101:ℤ))) (.branch 184 (.leaf (3313832311861122:ℤ)) (.branch 200 (.leaf (3762126737103525:ℤ)) (.leaf (4531208653927662:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1938669505136753:ℤ)) (.leaf (2208687825189742:ℤ))) (.branch 143 (.leaf (2357445255654768:ℤ)) (.branch 151 (.leaf (2523138813708506:ℤ)) (.leaf (2708605927366461:ℤ))))) (.branch 172 (.branch 165 (.leaf (2836079292691798:ℤ)) (.leaf (3091691396487248:ℤ))) (.branch 184 (.leaf (3317659009360881:ℤ)) (.branch 200 (.leaf (3773881507280913:ℤ)) (.leaf (4565004692511858:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1949556696264458:ℤ)) (.leaf (2226138621407709:ℤ))) (.branch 143 (.leaf (2379064729366125:ℤ)) (.branch 151 (.leaf (2549835562568366:ℤ)) (.leaf (2741501570755895:ℤ))))) (.branch 172 (.branch 165 (.leaf (2873537059870878:ℤ)) (.leaf (3138999864176227:ℤ))) (.branch 184 (.leaf (3374416388282233:ℤ)) (.branch 200 (.leaf (3851679364651111:ℤ)) (.leaf (4684881018381132:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 24 20) 8000 (endpointMeanRuns 24 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 24 20, EndpointRunConditions (endpointMeanCutoff 24 20) (endpointMeanBox 24 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 24 20 h) (endpointMeanCornerA 24 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 20, endpointJoint24Q (endpointMeanCornerK 24 20 h) (endpointMeanCornerA 24 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 24 20, endpointRunWeightQ (endpointMeanCutoff 24 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 24 20) = (421881449/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 24 20 h = (logRoundedQ ((endpointMeanCutoff 24 20:ℚ)/200)).2+(421881449/1000000000000000:ℚ)+((endpointMeanRuns 24 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 24 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 24 20) r*endpointJoint24Q (endpointMeanCornerK 24 20 h) (endpointMeanCornerA 24 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 24 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 24 20 h≤endpointMeanCorner 24 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 24 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint24_20

namespace EndpointAnalyticJoint24_21
private noncomputable def weights : IntegerLookupTree := (.branch 1270 (.branch 983 (.branch 825 (.leaf (40351429800000:ℤ)) (.leaf (17865616900000:ℤ))) (.branch 1146 (.leaf (13522169100000:ℤ)) (.leaf (7358364500000:ℤ)))) (.branch 1919 (.branch 1474 (.leaf (9113818200000:ℤ)) (.leaf (11582428300000:ℤ))) (.branch 2357 (.leaf (3983551800000:ℤ)) (.branch 3056 (.leaf (1955876700000:ℤ)) (.leaf (1121602400000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 156 (.branch 135 (.branch 127 (.leaf (1941279186614041:ℤ)) (.leaf (2211675319778464:ℤ))) (.branch 143 (.leaf (2360375388025940:ℤ)) (.leaf (2525737516022442:ℤ)))) (.branch 172 (.branch 165 (.leaf (2837169960915450:ℤ)) (.leaf (3090589893546101:ℤ))) (.branch 184 (.leaf (3313832311861122:ℤ)) (.branch 200 (.leaf (3762126737103525:ℤ)) (.leaf (4531208653927662:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1951785535259816:ℤ)) (.leaf (2228457917143620:ℤ))) (.branch 143 (.leaf (2381127307859587:ℤ)) (.leaf (2551307851576980:ℤ)))) (.branch 172 (.branch 165 (.leaf (2872899173102936:ℤ)) (.leaf (3135559995750686:ℤ))) (.branch 184 (.leaf (3367617668329090:ℤ)) (.branch 200 (.leaf (3835383352665034:ℤ)) (.leaf (4642818006509933:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1949556696264458:ℤ)) (.leaf (2226138621407709:ℤ))) (.branch 143 (.leaf (2379064729366125:ℤ)) (.leaf (2549835562568366:ℤ)))) (.branch 172 (.branch 165 (.leaf (2873537059870878:ℤ)) (.leaf (3138999864176227:ℤ))) (.branch 184 (.leaf (3374416388282233:ℤ)) (.branch 200 (.leaf (3851679364651111:ℤ)) (.leaf (4684881018381132:ℤ)))))), (.branch 156 (.branch 135 (.branch 127 (.leaf (1960505027741433:ℤ)) (.leaf (2243727296000870:ℤ))) (.branch 143 (.leaf (2400882469248215:ℤ)) (.leaf (2576814783560087:ℤ)))) (.branch 172 (.branch 165 (.leaf (2911489553810830:ℤ)) (.leaf (3187032236947599:ℤ))) (.branch 184 (.leaf (3432144753086380:ℤ)) (.branch 200 (.leaf (3931081010216486:ℤ)) (.leaf (4807905278255265:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 24 21) 8000 (endpointMeanRuns 24 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 24 21, EndpointRunConditions (endpointMeanCutoff 24 21) (endpointMeanBox 24 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 24 21 h) (endpointMeanCornerA 24 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 21, endpointJoint24Q (endpointMeanCornerK 24 21 h) (endpointMeanCornerA 24 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 24 21, endpointRunWeightQ (endpointMeanCutoff 24 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 24 21) = (420710761/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 24 21 h = (logRoundedQ ((endpointMeanCutoff 24 21:ℚ)/200)).2+(420710761/1000000000000000:ℚ)+((endpointMeanRuns 24 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 24 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 24 21) r*endpointJoint24Q (endpointMeanCornerK 24 21 h) (endpointMeanCornerA 24 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 24 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 24 21 h≤endpointMeanCorner 24 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 24 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint24_21

namespace EndpointAnalyticJoint24_22
private noncomputable def weights : IntegerLookupTree := (.branch 1146 (.branch 825 (.leaf (38173623100000:ℤ)) (.branch 983 (.leaf (17716795900000:ℤ)) (.leaf (13421370700000:ℤ)))) (.branch 1919 (.branch 1474 (.leaf (18633423400000:ℤ)) (.leaf (11514936100000:ℤ))) (.branch 3056 (.leaf (7965092100000:ℤ)) (.leaf (1116810400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 156 (.branch 127 (.leaf (1951785535259816:ℤ)) (.branch 143 (.leaf (2228457917143620:ℤ)) (.leaf (2551307851576980:ℤ)))) (.branch 184 (.branch 172 (.leaf (2872899173102936:ℤ)) (.leaf (3367617668329090:ℤ))) (.branch 200 (.leaf (3835383352665034:ℤ)) (.leaf (4642818006509933:ℤ))))), (.branch 156 (.branch 127 (.leaf (1962348745052937:ℤ)) (.branch 143 (.leaf (2245367863931087:ℤ)) (.leaf (2577137058869473:ℤ)))) (.branch 184 (.branch 172 (.leaf (2909078332463524:ℤ)) (.leaf (3422275991289668:ℤ))) (.branch 200 (.leaf (3910066430464139:ℤ)) (.leaf (4757176437436466:ℤ))))), (.branch 156 (.branch 127 (.leaf (1960505027741433:ℤ)) (.branch 143 (.leaf (2243727296000870:ℤ)) (.leaf (2576814783560087:ℤ)))) (.branch 184 (.branch 172 (.leaf (2911489553810830:ℤ)) (.leaf (3432144753086380:ℤ))) (.branch 200 (.leaf (3931081010216486:ℤ)) (.leaf (4807905278255265:ℤ))))), (.branch 156 (.branch 127 (.leaf (1971514842919986:ℤ)) (.branch 143 (.leaf (2261454938343370:ℤ)) (.leaf (2604079465456033:ℤ)))) (.branch 184 (.branch 172 (.leaf (2949943308658934:ℤ)) (.leaf (3490860715068677:ℤ))) (.branch 200 (.leaf (4012119505769003:ℤ)) (.leaf (4934160136400347:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 24 22) 8000 (endpointMeanRuns 24 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 24 22, EndpointRunConditions (endpointMeanCutoff 24 22) (endpointMeanBox 24 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 24 22 h) (endpointMeanCornerA 24 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 24 22, endpointJoint24Q (endpointMeanCornerK 24 22 h) (endpointMeanCornerA 24 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 24 22, endpointRunWeightQ (endpointMeanCutoff 24 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 24 22) = (209679919/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 24 22 h = (logRoundedQ ((endpointMeanCutoff 24 22:ℚ)/200)).2+(209679919/500000000000000:ℚ)+((endpointMeanRuns 24 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 24 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 24 22) r*endpointJoint24Q (endpointMeanCornerK 24 22 h) (endpointMeanCornerA 24 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 24 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 24 22 h≤endpointMeanCorner 24 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 24 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint24_22

namespace EndpointAnalyticJoint25_07
private noncomputable def weights : IntegerLookupTree := (.branch 1468 (.branch 807 (.leaf (73412407100000:ℤ)) (.leaf (87815457000000:ℤ))) (.branch 2989 (.leaf (33181638600000:ℤ)) (.leaf (1415630900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 127 (.leaf (1803750069083556:ℤ)) (.leaf (1995764403444523:ℤ))) (.branch 200 (.leaf (2379472614776194:ℤ)) (.leaf (3269166570786387:ℤ)))), (.branch 155 (.branch 127 (.leaf (1812669764039421:ℤ)) (.leaf (2009647709841973:ℤ))) (.branch 200 (.leaf (2406677462971304:ℤ)) (.leaf (3344669273492902:ℤ)))), (.branch 155 (.branch 127 (.leaf (1806460303467803:ℤ)) (.leaf (2000402012236859:ℤ))) (.branch 200 (.leaf (2390244865551529:ℤ)) (.leaf (3310773078037199:ℤ)))), (.branch 155 (.branch 127 (.leaf (1815730683812733:ℤ)) (.leaf (2014896141821442:ℤ))) (.branch 200 (.leaf (2418924400662697:ℤ)) (.leaf (3392541139336939:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 25 7) 8000 (endpointMeanRuns 25 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 25 7, EndpointRunConditions (endpointMeanCutoff 25 7) (endpointMeanBox 25 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 25 7 h) (endpointMeanCornerA 25 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 7, endpointJoint24Q (endpointMeanCornerK 25 7 h) (endpointMeanCornerA 25 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 25 7, endpointRunWeightQ (endpointMeanCutoff 25 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 25 7) = (219373811/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 25 7 h = (logRoundedQ ((endpointMeanCutoff 25 7:ℚ)/200)).2+(219373811/500000000000000:ℚ)+((endpointMeanRuns 25 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 25 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 25 7) r*endpointJoint24Q (endpointMeanCornerK 25 7 h) (endpointMeanCornerA 25 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 25 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 25 7 h≤endpointMeanCorner 25 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 25 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint25_07

namespace EndpointAnalyticJoint25_08
private noncomputable def weights : IntegerLookupTree := (.branch 1468 (.branch 807 (.leaf (69860501700000:ℤ)) (.leaf (87096826900000:ℤ))) (.branch 2989 (.leaf (32978390800000:ℤ)) (.leaf (1408898800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 127 (.leaf (1812669764039421:ℤ)) (.leaf (2009647709841973:ℤ))) (.branch 200 (.leaf (2406677462971304:ℤ)) (.leaf (3344669273492902:ℤ)))), (.branch 155 (.branch 127 (.leaf (1822849365111303:ℤ)) (.leaf (2025525894279985:ℤ))) (.branch 200 (.leaf (2437939082320633:ℤ)) (.leaf (3432499777678771:ℤ)))), (.branch 155 (.branch 127 (.leaf (1815730683812733:ℤ)) (.leaf (2014896141821442:ℤ))) (.branch 200 (.leaf (2418924400662697:ℤ)) (.leaf (3392541139336939:ℤ)))), (.branch 155 (.branch 127 (.leaf (1826312603366640:ℤ)) (.leaf (2031478002118868:ℤ))) (.branch 200 (.leaf (2451900286812082:ℤ)) (.leaf (3487819110252244:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 25 8) 8000 (endpointMeanRuns 25 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 25 8, EndpointRunConditions (endpointMeanCutoff 25 8) (endpointMeanBox 25 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 25 8 h) (endpointMeanCornerA 25 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 8, endpointJoint24Q (endpointMeanCornerK 25 8 h) (endpointMeanCornerA 25 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 25 8, endpointRunWeightQ (endpointMeanCutoff 25 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 25 8) = (437169113/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 25 8 h = (logRoundedQ ((endpointMeanCutoff 25 8:ℚ)/200)).2+(437169113/1000000000000000:ℚ)+((endpointMeanRuns 25 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 25 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 25 8) r*endpointJoint24Q (endpointMeanCornerK 25 8 h) (endpointMeanCornerA 25 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 25 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 25 8 h≤endpointMeanCorner 25 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 25 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint25_08

namespace EndpointAnalyticJoint25_09
private noncomputable def weights : IntegerLookupTree := (.branch 997 (.branch 807 (.leaf (66449883900000:ℤ)) (.leaf (25430597500000:ℤ))) (.branch 1468 (.leaf (41016519100000:ℤ)) (.branch 2989 (.leaf (32777892400000:ℤ)) (.leaf (1402257800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 127 (.leaf (1822849365111303:ℤ)) (.leaf (2025525894279985:ℤ))) (.branch 181 (.leaf (2437939082320633:ℤ)) (.branch 200 (.leaf (2945996148952659:ℤ)) (.leaf (3432499777678771:ℤ))))), (.branch 155 (.branch 127 (.leaf (1833086132844226:ℤ)) (.leaf (2041529531920475:ℤ))) (.branch 181 (.leaf (2469606775545410:ℤ)) (.branch 200 (.leaf (3003989153295260:ℤ)) (.leaf (3522636697487456:ℤ))))), (.branch 155 (.branch 127 (.leaf (1826312603366640:ℤ)) (.leaf (2031478002118868:ℤ))) (.branch 181 (.leaf (2451900286812082:ℤ)) (.branch 200 (.leaf (2976599984584000:ℤ)) (.leaf (3487819110252244:ℤ))))), (.branch 155 (.branch 127 (.leaf (1836956193421820:ℤ)) (.leaf (2048196325078171:ℤ))) (.branch 181 (.leaf (2485325715356031:ℤ)) (.branch 200 (.leaf (3038682751148660:ℤ)) (.leaf (3585772919534400:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 25 9) 8000 (endpointMeanRuns 25 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 25 9, EndpointRunConditions (endpointMeanCutoff 25 9) (endpointMeanBox 25 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 25 9 h) (endpointMeanCornerA 25 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 9, endpointJoint24Q (endpointMeanCornerK 25 9 h) (endpointMeanCornerA 25 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 25 9, endpointRunWeightQ (endpointMeanCutoff 25 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 25 9) = (435611957/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 25 9 h = (logRoundedQ ((endpointMeanCutoff 25 9:ℚ)/200)).2+(435611957/1000000000000000:ℚ)+((endpointMeanRuns 25 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 25 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 25 9) r*endpointJoint24Q (endpointMeanCornerK 25 9 h) (endpointMeanCornerA 25 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 25 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 25 9 h≤endpointMeanCorner 25 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 25 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint25_09

namespace EndpointAnalyticJoint25_10
private noncomputable def weights : IntegerLookupTree := (.branch 997 (.branch 807 (.leaf (63174820700000:ℤ)) (.leaf (25208906900000:ℤ))) (.branch 1468 (.leaf (40712040100000:ℤ)) (.branch 2989 (.leaf (32580069900000:ℤ)) (.leaf (1395705400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 127 (.leaf (1833086132844226:ℤ)) (.leaf (2041529531920475:ℤ))) (.branch 181 (.leaf (2469606775545410:ℤ)) (.branch 200 (.leaf (3003989153295260:ℤ)) (.leaf (3522636697487456:ℤ))))), (.branch 155 (.branch 127 (.leaf (1843380388275051:ℤ)) (.leaf (2057659613966564:ℤ))) (.branch 181 (.leaf (2501685817356156:ℤ)) (.branch 200 (.leaf (3063123770994651:ℤ)) (.leaf (3615140599040889:ℤ))))), (.branch 155 (.branch 127 (.leaf (1836956193421820:ℤ)) (.leaf (2048196325078171:ℤ))) (.branch 181 (.leaf (2485325715356031:ℤ)) (.branch 200 (.leaf (3038682751148660:ℤ)) (.leaf (3585772919534400:ℤ))))), (.branch 155 (.branch 127 (.leaf (1847661813388560:ℤ)) (.leaf (2065052233737288:ℤ))) (.branch 181 (.leaf (2519206814662505:ℤ)) (.branch 200 (.leaf (3102060374235621:ℤ)) (.leaf (3686477716883763:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 25 10) 8000 (endpointMeanRuns 25 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 25 10, EndpointRunConditions (endpointMeanCutoff 25 10) (endpointMeanBox 25 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 25 10 h) (endpointMeanCornerA 25 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 10, endpointJoint24Q (endpointMeanCornerK 25 10 h) (endpointMeanCornerA 25 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 25 10, endpointRunWeightQ (endpointMeanCutoff 25 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 25 10) = (434075583/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 25 10 h = (logRoundedQ ((endpointMeanCutoff 25 10:ℚ)/200)).2+(434075583/1000000000000000:ℚ)+((endpointMeanRuns 25 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 25 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 25 10) r*endpointJoint24Q (endpointMeanCornerK 25 10 h) (endpointMeanCornerA 25 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 25 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 25 10 h≤endpointMeanCorner 25 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 25 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint25_10

namespace EndpointAnalyticJoint25_11
private noncomputable def weights : IntegerLookupTree := (.branch 997 (.branch 807 (.leaf (60029831500000:ℤ)) (.leaf (24990136000000:ℤ))) (.branch 1468 (.leaf (40411571200000:ℤ)) (.branch 2989 (.leaf (32384852800000:ℤ)) (.leaf (1389239300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 127 (.leaf (1843380388275051:ℤ)) (.leaf (2057659613966564:ℤ))) (.branch 181 (.leaf (2501685817356156:ℤ)) (.branch 200 (.leaf (3063123770994651:ℤ)) (.leaf (3615140599040889:ℤ))))), (.branch 155 (.branch 127 (.leaf (1853732454243510:ℤ)) (.leaf (2073917139452849:ℤ))) (.branch 181 (.leaf (2534181550979406:ℤ)) (.branch 200 (.leaf (3123422475124446:ℤ)) (.leaf (3710073638918094:ℤ))))), (.branch 155 (.branch 127 (.leaf (1847661813388560:ℤ)) (.leaf (2065052233737288:ℤ))) (.branch 181 (.leaf (2519206814662505:ℤ)) (.branch 200 (.leaf (3102060374235621:ℤ)) (.leaf (3686477716883763:ℤ))))), (.branch 155 (.branch 127 (.leaf (1858429824771751:ℤ)) (.leaf (2082046860376337:ℤ))) (.branch 181 (.leaf (2553549796644209:ℤ)) (.branch 200 (.leaf (3166759860589364:ℤ)) (.leaf (3790010762545765:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 25 11) 8000 (endpointMeanRuns 25 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 25 11, EndpointRunConditions (endpointMeanCutoff 25 11) (endpointMeanBox 25 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 25 11 h) (endpointMeanCornerA 25 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 11, endpointJoint24Q (endpointMeanCornerK 25 11 h) (endpointMeanCornerA 25 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 25 11, endpointRunWeightQ (endpointMeanCutoff 25 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 25 11) = (108139861/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 25 11 h = (logRoundedQ ((endpointMeanCutoff 25 11:ℚ)/200)).2+(108139861/250000000000000:ℚ)+((endpointMeanRuns 25 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 25 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 25 11) r*endpointJoint24Q (endpointMeanCornerK 25 11 h) (endpointMeanCornerA 25 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 25 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 25 11 h≤endpointMeanCorner 25 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 25 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint25_11

namespace EndpointAnalyticJoint25_12
private noncomputable def weights : IntegerLookupTree := (.branch 1468 (.branch 807 (.leaf (57009675800000:ℤ)) (.branch 997 (.leaf (24774209000000:ℤ)) (.leaf (40115008200000:ℤ)))) (.branch 1877 (.leaf (11875456900000:ℤ)) (.branch 2989 (.leaf (9402627600000:ℤ)) (.leaf (1382857300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 127 (.leaf (1853732454243510:ℤ)) (.branch 143 (.leaf (2073917139452849:ℤ)) (.leaf (2319385343595954:ℤ)))) (.branch 181 (.leaf (2534181550979406:ℤ)) (.branch 200 (.leaf (3123422475124446:ℤ)) (.leaf (3710073638918094:ℤ))))), (.branch 155 (.branch 127 (.leaf (1864142655402349:ℤ)) (.branch 143 (.leaf (2090303115307283:ℤ)) (.leaf (2343926224062299:ℤ)))) (.branch 181 (.leaf (2567099389047749:ℤ)) (.branch 200 (.leaf (3184908181148899:ℤ)) (.leaf (3807499605920381:ℤ))))), (.branch 155 (.branch 127 (.leaf (1858429824771751:ℤ)) (.branch 143 (.leaf (2082046860376337:ℤ)) (.leaf (2332773600724936:ℤ)))) (.branch 181 (.leaf (2553549796644209:ℤ)) (.branch 200 (.leaf (3166759860589364:ℤ)) (.leaf (3790010762545765:ℤ))))), (.branch 155 (.branch 127 (.leaf (1869260591183116:ℤ)) (.branch 143 (.leaf (2099181346593699:ℤ)) (.leaf (2358587151286266:ℤ)))) (.branch 181 (.leaf (2588360957897475:ℤ)) (.branch 200 (.leaf (3232808780232423:ℤ)) (.leaf (3896451486584594:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 25 12) 8000 (endpointMeanRuns 25 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 25 12, EndpointRunConditions (endpointMeanCutoff 25 12) (endpointMeanBox 25 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 25 12 h) (endpointMeanCornerA 25 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 12, endpointJoint24Q (endpointMeanCornerK 25 12 h) (endpointMeanCornerA 25 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 25 12, endpointRunWeightQ (endpointMeanCutoff 25 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 25 12) = (431063013/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 25 12 h = (logRoundedQ ((endpointMeanCutoff 25 12:ℚ)/200)).2+(431063013/1000000000000000:ℚ)+((endpointMeanRuns 25 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 25 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 25 12) r*endpointJoint24Q (endpointMeanCornerK 25 12 h) (endpointMeanCornerA 25 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 25 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 25 12 h≤endpointMeanCorner 25 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 25 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint25_12

namespace EndpointAnalyticJoint25_13
private noncomputable def weights : IntegerLookupTree := (.branch 1170 (.branch 807 (.leaf (54109341200000:ℤ)) (.branch 997 (.leaf (24561053000000:ℤ)) (.leaf (15227387500000:ℤ)))) (.branch 1877 (.branch 1468 (.leaf (17647990200000:ℤ)) (.leaf (11802704400000:ℤ))) (.branch 2989 (.leaf (9351830600000:ℤ)) (.leaf (1376557200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 127 (.leaf (1864142655402349:ℤ)) (.branch 143 (.leaf (2090303115307283:ℤ)) (.leaf (2343926224062299:ℤ)))) (.branch 181 (.branch 169 (.leaf (2567099389047749:ℤ)) (.leaf (2873025384574363:ℤ))) (.branch 200 (.leaf (3184908181148899:ℤ)) (.leaf (3807499605920381:ℤ))))), (.branch 155 (.branch 127 (.leaf (1874611318227505:ℤ)) (.branch 143 (.leaf (2106818556413531:ℤ)) (.leaf (2368726765915108:ℤ)))) (.branch 181 (.branch 169 (.leaf (2600444814501325:ℤ)) (.leaf (2919894793321004:ℤ))) (.branch 200 (.leaf (3247604255631490:ℤ)) (.leaf (3907483963933231:ℤ))))), (.branch 155 (.branch 127 (.leaf (1869260591183116:ℤ)) (.branch 143 (.leaf (2099181346593699:ℤ)) (.leaf (2358587151286266:ℤ)))) (.branch 181 (.branch 169 (.leaf (2588360957897475:ℤ)) (.leaf (2905858811599381:ℤ))) (.branch 200 (.leaf (3232808780232423:ℤ)) (.leaf (3896451486584594:ℤ))))), (.branch 155 (.branch 127 (.leaf (1880154478353462:ℤ)) (.branch 143 (.leaf (2116456843382684:ℤ)) (.leaf (2384686344394466:ℤ)))) (.branch 181 (.branch 169 (.leaf (2623646680856716:ℤ)) (.leaf (2955846442869629:ℤ))) (.branch 200 (.leaf (3300235278213605:ℤ)) (.leaf (4005881549821581:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 25 13) 8000 (endpointMeanRuns 25 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 25 13, EndpointRunConditions (endpointMeanCutoff 25 13) (endpointMeanBox 25 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 25 13 h) (endpointMeanCornerA 25 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 13, endpointJoint24Q (endpointMeanCornerK 25 13 h) (endpointMeanCornerA 25 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 25 13, endpointRunWeightQ (endpointMeanCutoff 25 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 25 13) = (214792893/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 25 13 h = (logRoundedQ ((endpointMeanCutoff 25 13:ℚ)/200)).2+(214792893/500000000000000:ℚ)+((endpointMeanRuns 25 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 25 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 25 13) r*endpointJoint24Q (endpointMeanCornerK 25 13 h) (endpointMeanCornerA 25 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 25 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 25 13 h≤endpointMeanCorner 25 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 25 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint25_13

namespace EndpointAnalyticJoint25_14
private noncomputable def weights : IntegerLookupTree := (.branch 1170 (.branch 807 (.leaf (51715067100000:ℤ)) (.branch 1035 (.leaf (29394632500000:ℤ)) (.leaf (10942387200000:ℤ)))) (.branch 1877 (.branch 1468 (.leaf (17544423800000:ℤ)) (.leaf (11741079700000:ℤ))) (.branch 2989 (.leaf (9308803200000:ℤ)) (.leaf (1371220700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 127 (.leaf (1874611318227505:ℤ)) (.branch 143 (.leaf (2106818556413531:ℤ)) (.leaf (2368726765915108:ℤ)))) (.branch 178 (.branch 169 (.leaf (2600444814501325:ℤ)) (.leaf (2919894793321004:ℤ))) (.branch 200 (.leaf (3160238937311023:ℤ)) (.leaf (3907483963933231:ℤ))))), (.branch 155 (.branch 127 (.leaf (1885138771028320:ℤ)) (.branch 143 (.leaf (2123464485673840:ℤ)) (.leaf (2393789716571525:ℤ)))) (.branch 178 (.branch 169 (.leaf (2634223381501117:ℤ)) (.leaf (2967528811210349:ℤ))) (.branch 200 (.leaf (3219626394360677:ℤ)) (.leaf (4010093895913747:ℤ))))), (.branch 155 (.branch 127 (.leaf (1880154478353462:ℤ)) (.branch 143 (.leaf (2116456843382684:ℤ)) (.leaf (2384686344394466:ℤ)))) (.branch 178 (.branch 169 (.leaf (2623646680856716:ℤ)) (.leaf (2955846442869629:ℤ))) (.branch 200 (.leaf (3208050855623495:ℤ)) (.leaf (4005881549821581:ℤ))))), (.branch 155 (.branch 127 (.leaf (1891111854145052:ℤ)) (.branch 143 (.leaf (2133874511208863:ℤ)) (.leaf (2411074340857052:ℤ)))) (.branch 178 (.branch 169 (.leaf (2659413434964628:ℤ)) (.leaf (3006693979400943:ℤ))) (.branch 200 (.leaf (3271844181036773:ℤ)) (.leaf (4118384906484978:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 25 14) 8000 (endpointMeanRuns 25 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 25 14, EndpointRunConditions (endpointMeanCutoff 25 14) (endpointMeanBox 25 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 25 14 h) (endpointMeanCornerA 25 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 14, endpointJoint24Q (endpointMeanCornerK 25 14 h) (endpointMeanCornerA 25 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 25 14, endpointRunWeightQ (endpointMeanCutoff 25 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 25 14) = (428334507/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 25 14 h = (logRoundedQ ((endpointMeanCutoff 25 14:ℚ)/200)).2+(428334507/1000000000000000:ℚ)+((endpointMeanRuns 25 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 25 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 25 14) r*endpointJoint24Q (endpointMeanCornerK 25 14 h) (endpointMeanCornerA 25 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 25 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 25 14 h≤endpointMeanCorner 25 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 25 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint25_14

namespace EndpointAnalyticJoint25_15
private noncomputable def weights : IntegerLookupTree := (.branch 1170 (.branch 897 (.branch 807 (.leaf (49024690700000:ℤ)) (.leaf (11232184200000:ℤ))) (.branch 1035 (.leaf (14658901500000:ℤ)) (.leaf (10860706500000:ℤ)))) (.branch 1877 (.branch 1468 (.leaf (17425002100000:ℤ)) (.leaf (11670020700000:ℤ))) (.branch 2306 (.leaf (4613174900000:ℤ)) (.branch 2989 (.leaf (2315201800000:ℤ)) (.leaf (1365067200000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 135 (.branch 127 (.leaf (1885138771028320:ℤ)) (.leaf (2123464485673840:ℤ))) (.branch 143 (.leaf (2252259389370479:ℤ)) (.leaf (2393789716571525:ℤ)))) (.branch 178 (.branch 169 (.leaf (2634223381501117:ℤ)) (.leaf (2967528811210349:ℤ))) (.branch 190 (.leaf (3219626394360677:ℤ)) (.branch 200 (.leaf (3614913824629351:ℤ)) (.leaf (4010093895913747:ℤ)))))), (.branch 155 (.branch 135 (.branch 127 (.leaf (1895725343957874:ℤ)) (.leaf (2140241934072371:ℤ))) (.branch 143 (.leaf (2272914232804425:ℤ)) (.leaf (2419117852518471:ℤ)))) (.branch 178 (.branch 169 (.leaf (2668440716354095:ℤ)) (.leaf (3015939911775914:ℤ))) (.branch 190 (.leaf (3280129865143714:ℤ)) (.branch 200 (.leaf (3696571930294827:ℤ)) (.leaf (4115398349033256:ℤ)))))), (.branch 155 (.branch 135 (.branch 127 (.leaf (1891111854145052:ℤ)) (.leaf (2133874511208863:ℤ))) (.branch 143 (.leaf (2265689485179153:ℤ)) (.leaf (2411074340857052:ℤ)))) (.branch 178 (.branch 169 (.leaf (2659413434964628:ℤ)) (.leaf (3006693979400943:ℤ))) (.branch 190 (.leaf (3271844181036773:ℤ)) (.branch 200 (.leaf (3692193329021298:ℤ)) (.leaf (4118384906484978:ℤ)))))), (.branch 155 (.branch 135 (.branch 127 (.leaf (1902133088564017:ℤ)) (.leaf (2151435520088022:ℤ))) (.branch 143 (.leaf (2287373911101549:ℤ)) (.leaf (2437754336457780:ℤ)))) (.branch 178 (.branch 169 (.leaf (2695667777858318:ℤ)) (.leaf (3058416213593751:ℤ))) (.branch 190 (.leaf (3336906061267427:ℤ)) (.branch 200 (.leaf (3780925136838736:ℤ)) (.leaf (4234047868619263:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 25 15) 8000 (endpointMeanRuns 25 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 25 15, EndpointRunConditions (endpointMeanCutoff 25 15) (endpointMeanBox 25 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 25 15 h) (endpointMeanCornerA 25 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 15, endpointJoint24Q (endpointMeanCornerK 25 15 h) (endpointMeanCornerA 25 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 25 15, endpointRunWeightQ (endpointMeanCutoff 25 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 25 15) = (85378333/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 25 15 h = (logRoundedQ ((endpointMeanCutoff 25 15:ℚ)/200)).2+(85378333/200000000000000:ℚ)+((endpointMeanRuns 25 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 25 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 25 15) r*endpointJoint24Q (endpointMeanCornerK 25 15 h) (endpointMeanCornerA 25 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 25 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 25 15 h≤endpointMeanCorner 25 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 25 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint25_15

namespace EndpointAnalyticJoint25_16
private noncomputable def weights : IntegerLookupTree := (.branch 1302 (.branch 897 (.branch 807 (.leaf (46440973200000:ℤ)) (.leaf (11133633700000:ℤ))) (.branch 1035 (.leaf (14540500900000:ℤ)) (.branch 1170 (.leaf (10780036900000:ℤ)) (.leaf (7950361100000:ℤ))))) (.branch 1877 (.branch 1468 (.leaf (7447498600000:ℤ)) (.leaf (11599841300000:ℤ))) (.branch 2306 (.leaf (4588214300000:ℤ)) (.branch 2989 (.leaf (2303751100000:ℤ)) (.leaf (1358989900000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 135 (.branch 127 (.leaf (1895725343957874:ℤ)) (.leaf (2140241934072371:ℤ))) (.branch 143 (.leaf (2272914232804425:ℤ)) (.branch 155 (.leaf (2419117852518471:ℤ)) (.leaf (2668440716354095:ℤ))))) (.branch 178 (.branch 169 (.leaf (2833581839758415:ℤ)) (.leaf (3015939911775914:ℤ))) (.branch 190 (.leaf (3280129865143714:ℤ)) (.branch 200 (.leaf (3696571930294827:ℤ)) (.leaf (4115398349033256:ℤ)))))), (.branch 162 (.branch 135 (.branch 127 (.leaf (1906371369023326:ℤ)) (.leaf (2157151940739084:ℤ))) (.branch 143 (.leaf (2293758496053559:ℤ)) (.branch 155 (.leaf (2444713979620243:ℤ)) (.leaf (2703102518450300:ℤ))))) (.branch 178 (.branch 169 (.leaf (2874885731309072:ℤ)) (.leaf (3065140772039558:ℤ))) (.branch 190 (.leaf (3341770321877426:ℤ)) (.branch 200 (.leaf (3780074629370926:ℤ)) (.leaf (4223468081005230:ℤ)))))), (.branch 162 (.branch 135 (.branch 127 (.leaf (1902133088564017:ℤ)) (.leaf (2151435520088022:ℤ))) (.branch 143 (.leaf (2287373911101549:ℤ)) (.branch 155 (.leaf (2437754336457780:ℤ)) (.leaf (2695667777858318:ℤ))))) (.branch 178 (.branch 169 (.leaf (2867565682691404:ℤ)) (.leaf (3058416213593751:ℤ))) (.branch 190 (.leaf (3336906061267427:ℤ)) (.branch 200 (.leaf (3780925136838736:ℤ)) (.leaf (4234047868619263:ℤ)))))), (.branch 162 (.branch 135 (.branch 127 (.leaf (1913218553772849:ℤ)) (.leaf (2169141049664729:ℤ))) (.branch 143 (.leaf (2309265873992563:ℤ)) (.branch 155 (.leaf (2464729562343695:ℤ)) (.leaf (2732416356571595:ℤ))))) (.branch 178 (.branch 169 (.leaf (2911533571539189:ℤ)) (.leaf (3111028192312677:ℤ))) (.branch 190 (.leaf (3403261722016019:ℤ)) (.branch 200 (.leaf (3871789371920119:ℤ)) (.leaf (4352959172303311:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 25 16) 8000 (endpointMeanRuns 25 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 25 16, EndpointRunConditions (endpointMeanCutoff 25 16) (endpointMeanBox 25 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 25 16 h) (endpointMeanCornerA 25 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 16, endpointJoint24Q (endpointMeanCornerK 25 16 h) (endpointMeanCornerA 25 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 25 16, endpointRunWeightQ (endpointMeanCutoff 25 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 25 16) = (85093337/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 25 16 h = (logRoundedQ ((endpointMeanCutoff 25 16:ℚ)/200)).2+(85093337/200000000000000:ℚ)+((endpointMeanRuns 25 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 25 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 25 16) r*endpointJoint24Q (endpointMeanCornerK 25 16 h) (endpointMeanCornerA 25 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 25 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 25 16 h≤endpointMeanCorner 25 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 25 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint25_16

namespace EndpointAnalyticJoint25_17
private noncomputable def weights : IntegerLookupTree := (.branch 1302 (.branch 897 (.branch 807 (.leaf (43959682100000:ℤ)) (.leaf (11036288300000:ℤ))) (.branch 1035 (.leaf (14423548000000:ℤ)) (.branch 1170 (.leaf (10700353600000:ℤ)) (.leaf (7895432500000:ℤ))))) (.branch 1877 (.branch 1468 (.leaf (7399109600000:ℤ)) (.leaf (11530520000000:ℤ))) (.branch 2306 (.leaf (4563559000000:ℤ)) (.branch 2989 (.leaf (2292440400000:ℤ)) (.leaf (1352986900000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 135 (.branch 127 (.leaf (1906371369023326:ℤ)) (.leaf (2157151940739084:ℤ))) (.branch 143 (.leaf (2293758496053559:ℤ)) (.branch 155 (.leaf (2444713979620243:ℤ)) (.leaf (2703102518450300:ℤ))))) (.branch 178 (.branch 169 (.leaf (2874885731309072:ℤ)) (.leaf (3065140772039558:ℤ))) (.branch 190 (.leaf (3341770321877426:ℤ)) (.branch 200 (.leaf (3780074629370926:ℤ)) (.leaf (4223468081005230:ℤ)))))), (.branch 162 (.branch 135 (.branch 127 (.leaf (1917077180096308:ℤ)) (.leaf (2174195553014077:ℤ))) (.branch 143 (.leaf (2314793916234229:ℤ)) (.branch 155 (.leaf (2470580933429327:ℤ)) (.leaf (2738214561212228:ℤ))))) (.branch 178 (.branch 169 (.leaf (2916791691744167:ℤ)) (.leaf (3115144275831086:ℤ))) (.branch 190 (.leaf (3404569130890638:ℤ)) (.branch 200 (.leaf (3865463589795237:ℤ)) (.leaf (4334375707629917:ℤ)))))), (.branch 162 (.branch 135 (.branch 127 (.leaf (1913218553772849:ℤ)) (.leaf (2169141049664729:ℤ))) (.branch 143 (.leaf (2309265873992563:ℤ)) (.branch 155 (.leaf (2464729562343695:ℤ)) (.leaf (2732416356571595:ℤ))))) (.branch 178 (.branch 169 (.leaf (2911533571539189:ℤ)) (.leaf (3111028192312677:ℤ))) (.branch 190 (.leaf (3403261722016019:ℤ)) (.branch 200 (.leaf (3871789371920119:ℤ)) (.leaf (4352959172303311:ℤ)))))), (.branch 162 (.branch 135 (.branch 127 (.leaf (1924368624102969:ℤ)) (.leaf (2186992289291620:ℤ))) (.branch 143 (.leaf (2331367360143813:ℤ)) (.branch 155 (.leaf (2492003285416434:ℤ)) (.leaf (2769665908753685:ℤ))))) (.branch 178 (.branch 169 (.leaf (2956175612425198:ℤ)) (.leaf (3164545221263946:ℤ))) (.branch 190 (.leaf (3470936890605864:ℤ)) (.branch 200 (.leaf (3964837281345241:ℤ)) (.leaf (4475210045728329:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 25 17) 8000 (endpointMeanRuns 25 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 25 17, EndpointRunConditions (endpointMeanCutoff 25 17) (endpointMeanBox 25 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 25 17 h) (endpointMeanCornerA 25 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 17, endpointJoint24Q (endpointMeanCornerK 25 17 h) (endpointMeanCornerA 25 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 25 17, endpointRunWeightQ (endpointMeanCutoff 25 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 25 17) = (53007391/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 25 17 h = (logRoundedQ ((endpointMeanCutoff 25 17:ℚ)/200)).2+(53007391/125000000000000:ℚ)+((endpointMeanRuns 25 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 25 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 25 17) r*endpointJoint24Q (endpointMeanCornerK 25 17 h) (endpointMeanCornerA 25 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 25 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 25 17 h≤endpointMeanCorner 25 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 25 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint25_17

namespace EndpointAnalyticJoint25_18
private noncomputable def weights : IntegerLookupTree := (.branch 1302 (.branch 917 (.branch 807 (.leaf (41576764200000:ℤ)) (.leaf (13453101600000:ℤ))) (.branch 1035 (.leaf (11750737300000:ℤ)) (.branch 1170 (.leaf (10621633000000:ℤ)) (.leaf (7841167300000:ℤ))))) (.branch 1877 (.branch 1468 (.leaf (7351305100000:ℤ)) (.leaf (11462036100000:ℤ))) (.branch 2306 (.leaf (4539201500000:ℤ)) (.branch 2989 (.leaf (2281266400000:ℤ)) (.leaf (1347056400000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 135 (.branch 127 (.leaf (1917077180096308:ℤ)) (.leaf (2174195553014077:ℤ))) (.branch 143 (.leaf (2314793916234229:ℤ)) (.branch 155 (.leaf (2470580933429327:ℤ)) (.leaf (2738214561212228:ℤ))))) (.branch 178 (.branch 169 (.leaf (2916791691744167:ℤ)) (.leaf (3115144275831086:ℤ))) (.branch 188 (.leaf (3404569130890638:ℤ)) (.branch 200 (.leaf (3781725266491901:ℤ)) (.leaf (4334375707629917:ℤ)))))), (.branch 162 (.branch 135 (.branch 127 (.leaf (1927843112923422:ℤ)) (.leaf (2191373826512464:ℤ))) (.branch 143 (.leaf (2336022246393409:ℤ)) (.branch 155 (.leaf (2496721579500550:ℤ)) (.leaf (2773782693056420:ℤ))))) (.branch 178 (.branch 169 (.leaf (2959308497160286:ℤ)) (.leaf (3165963517162060:ℤ))) (.branch 188 (.leaf (3468548060029893:ℤ)) (.branch 200 (.leaf (3864595463525387:ℤ)) (.leaf (4448195751587375:ℤ)))))), (.branch 162 (.branch 135 (.branch 127 (.leaf (1924368624102969:ℤ)) (.leaf (2186992289291620:ℤ))) (.branch 143 (.leaf (2331367360143813:ℤ)) (.branch 155 (.leaf (2492003285416434:ℤ)) (.leaf (2769665908753685:ℤ))))) (.branch 178 (.branch 169 (.leaf (2956175612425198:ℤ)) (.leaf (3164545221263946:ℤ))) (.branch 188 (.leaf (3470936890605864:ℤ)) (.branch 200 (.leaf (3874541772547952:ℤ)) (.leaf (4475210045728329:ℤ)))))), (.branch 162 (.branch 135 (.branch 127 (.leaf (1935583676067372:ℤ)) (.leaf (2204990438109255:ℤ))) (.branch 143 (.leaf (2353680374857273:ℤ)) (.branch 155 (.leaf (2519578808727872:ℤ)) (.leaf (2807423263904543:ℤ))))) (.branch 178 (.branch 169 (.leaf (3001502142006084:ℤ)) (.leaf (3218982869448066:ℤ))) (.branch 188 (.leaf (3539957805958014:ℤ)) (.branch 200 (.leaf (3964783093166241:ℤ)) (.leaf (4600894279187657:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 25 18) 8000 (endpointMeanRuns 25 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 25 18, EndpointRunConditions (endpointMeanCutoff 25 18) (endpointMeanBox 25 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 25 18 h) (endpointMeanCornerA 25 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 18, endpointJoint24Q (endpointMeanCornerK 25 18 h) (endpointMeanCornerA 25 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 25 18, endpointRunWeightQ (endpointMeanCutoff 25 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 25 18) = (211334287/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 25 18 h = (logRoundedQ ((endpointMeanCutoff 25 18:ℚ)/200)).2+(211334287/500000000000000:ℚ)+((endpointMeanRuns 25 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 25 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 25 18) r*endpointJoint24Q (endpointMeanCornerK 25 18 h) (endpointMeanCornerA 25 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 25 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 25 18 h≤endpointMeanCorner 25 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 25 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint25_18

namespace EndpointAnalyticJoint25_19
private noncomputable def weights : IntegerLookupTree := (.branch 1302 (.branch 917 (.branch 807 (.leaf (39288337000000:ℤ)) (.leaf (13337073100000:ℤ))) (.branch 1035 (.leaf (11657761500000:ℤ)) (.branch 1170 (.leaf (10543851900000:ℤ)) (.leaf (7787549900000:ℤ))))) (.branch 1877 (.branch 1468 (.leaf (7304071200000:ℤ)) (.leaf (11394369600000:ℤ))) (.branch 2306 (.leaf (4515134700000:ℤ)) (.branch 2989 (.leaf (2270225700000:ℤ)) (.leaf (1341196700000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 135 (.branch 127 (.leaf (1927843112923422:ℤ)) (.leaf (2191373826512464:ℤ))) (.branch 143 (.leaf (2336022246393409:ℤ)) (.branch 155 (.leaf (2496721579500550:ℤ)) (.leaf (2773782693056420:ℤ))))) (.branch 178 (.branch 169 (.leaf (2959308497160286:ℤ)) (.leaf (3165963517162060:ℤ))) (.branch 188 (.leaf (3468548060029893:ℤ)) (.branch 200 (.leaf (3864595463525387:ℤ)) (.leaf (4448195751587375:ℤ)))))), (.branch 162 (.branch 135 (.branch 127 (.leaf (1938669505136753:ℤ)) (.leaf (2208687825189742:ℤ))) (.branch 143 (.leaf (2357445255654768:ℤ)) (.branch 155 (.leaf (2523138813708506:ℤ)) (.leaf (2809812838367635:ℤ))))) (.branch 178 (.branch 169 (.leaf (3002445051579362:ℤ)) (.leaf (3217611803654594:ℤ))) (.branch 188 (.leaf (3533729286204818:ℤ)) (.branch 200 (.leaf (3949281622605939:ℤ)) (.leaf (4565004692511858:ℤ)))))), (.branch 162 (.branch 135 (.branch 127 (.leaf (1935583676067372:ℤ)) (.leaf (2204990438109255:ℤ))) (.branch 143 (.leaf (2353680374857273:ℤ)) (.branch 155 (.leaf (2519578808727872:ℤ)) (.leaf (2807423263904543:ℤ))))) (.branch 178 (.branch 169 (.leaf (3001502142006084:ℤ)) (.leaf (3218982869448066:ℤ))) (.branch 188 (.leaf (3539957805958014:ℤ)) (.branch 200 (.leaf (3964783093166241:ℤ)) (.leaf (4600894279187657:ℤ)))))), (.branch 162 (.branch 135 (.branch 127 (.leaf (1946864088373341:ℤ)) (.leaf (2223136705126689:ℤ))) (.branch 143 (.leaf (2376206942627240:ℤ)) (.branch 155 (.leaf (2547459471880157:ℤ)) (.leaf (2845695344626984:ℤ))))) (.branch 178 (.branch 169 (.leaf (3047523655428668:ℤ)) (.leaf (3274356973689095:ℤ))) (.branch 188 (.leaf (3610351228764548:ℤ)) (.branch 200 (.leaf (4057126209667760:ℤ)) (.leaf (4730108297032268:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 25 19) 8000 (endpointMeanRuns 25 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 25 19, EndpointRunConditions (endpointMeanCutoff 25 19) (endpointMeanBox 25 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 25 19 h) (endpointMeanCornerA 25 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 19, endpointJoint24Q (endpointMeanCornerK 25 19 h) (endpointMeanCornerA 25 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 25 19, endpointRunWeightQ (endpointMeanCutoff 25 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 25 19) = (421294617/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 25 19 h = (logRoundedQ ((endpointMeanCutoff 25 19:ℚ)/200)).2+(421294617/1000000000000000:ℚ)+((endpointMeanRuns 25 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 25 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 25 19) r*endpointJoint24Q (endpointMeanCornerK 25 19 h) (endpointMeanCornerA 25 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 25 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 25 19 h≤endpointMeanCorner 25 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 25 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint25_19

namespace EndpointAnalyticJoint25_20
private noncomputable def weights : IntegerLookupTree := (.branch 1302 (.branch 917 (.branch 807 (.leaf (37090681100000:ℤ)) (.leaf (13222413200000:ℤ))) (.branch 1035 (.leaf (11565882300000:ℤ)) (.branch 1170 (.leaf (10466988200000:ℤ)) (.leaf (7734564900000:ℤ))))) (.branch 1877 (.branch 1468 (.leaf (7257394500000:ℤ)) (.leaf (11327501200000:ℤ))) (.branch 2306 (.leaf (4491351800000:ℤ)) (.branch 2989 (.leaf (2259315300000:ℤ)) (.leaf (1335406100000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 135 (.branch 127 (.leaf (1938669505136753:ℤ)) (.leaf (2208687825189742:ℤ))) (.branch 143 (.leaf (2357445255654768:ℤ)) (.branch 155 (.leaf (2523138813708506:ℤ)) (.leaf (2809812838367635:ℤ))))) (.branch 178 (.branch 169 (.leaf (3002445051579362:ℤ)) (.leaf (3217611803654594:ℤ))) (.branch 188 (.leaf (3533729286204818:ℤ)) (.branch 200 (.leaf (3949281622605939:ℤ)) (.leaf (4565004692511858:ℤ)))))), (.branch 162 (.branch 135 (.branch 127 (.leaf (1949556696264458:ℤ)) (.leaf (2226138621407709:ℤ))) (.branch 143 (.leaf (2379064729366125:ℤ)) (.branch 155 (.leaf (2549835562568366:ℤ)) (.leaf (2846310998485636:ℤ))))) (.branch 178 (.branch 169 (.leaf (3046210388813390:ℤ)) (.leaf (3270102660026147:ℤ))) (.branch 188 (.leaf (3600135403075260:ℤ)) (.branch 200 (.leaf (4035823537510735:ℤ)) (.leaf (4684881018381132:ℤ)))))), (.branch 162 (.branch 135 (.branch 127 (.leaf (1946864088373341:ℤ)) (.leaf (2223136705126689:ℤ))) (.branch 143 (.leaf (2376206942627240:ℤ)) (.branch 155 (.leaf (2547459471880157:ℤ)) (.leaf (2845695344626984:ℤ))))) (.branch 178 (.branch 169 (.leaf (3047523655428668:ℤ)) (.leaf (3274356973689095:ℤ))) (.branch 188 (.leaf (3610351228764548:ℤ)) (.branch 200 (.leaf (4057126209667760:ℤ)) (.leaf (4730108297032268:ℤ)))))), (.branch 162 (.branch 135 (.branch 127 (.leaf (1958210241935223:ℤ)) (.leaf (2241432309302674:ℤ))) (.branch 143 (.leaf (2398949107324012:ℤ)) (.branch 155 (.leaf (2575648651430148:ℤ)) (.leaf (2884489167895927:ℤ))))) (.branch 178 (.branch 169 (.leaf (3094250808760032:ℤ)) (.leaf (3330683643241851:ℤ))) (.branch 188 (.leaf (3682144451864202:ℤ)) (.branch 200 (.leaf (4151620074637689:ℤ)) (.leaf (4862951231647052:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 25 20) 8000 (endpointMeanRuns 25 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 25 20, EndpointRunConditions (endpointMeanCutoff 25 20) (endpointMeanBox 25 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 25 20 h) (endpointMeanCornerA 25 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 20, endpointJoint24Q (endpointMeanCornerK 25 20 h) (endpointMeanCornerA 25 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 25 20, endpointRunWeightQ (endpointMeanCutoff 25 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 25 20) = (83987373/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 25 20 h = (logRoundedQ ((endpointMeanCutoff 25 20:ℚ)/200)).2+(83987373/200000000000000:ℚ)+((endpointMeanRuns 25 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 25 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 25 20) r*endpointJoint24Q (endpointMeanCornerK 25 20 h) (endpointMeanCornerA 25 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 25 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 25 20 h≤endpointMeanCorner 25 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 25 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint25_20

namespace EndpointAnalyticJoint25_21
private noncomputable def weights : IntegerLookupTree := (.branch 1170 (.branch 917 (.branch 807 (.leaf (34980232000000:ℤ)) (.leaf (13109089900000:ℤ))) (.branch 1035 (.leaf (11475074100000:ℤ)) (.leaf (10391020500000:ℤ)))) (.branch 1877 (.branch 1468 (.leaf (16738295200000:ℤ)) (.leaf (11261412300000:ℤ))) (.branch 2306 (.leaf (4467846100000:ℤ)) (.branch 2989 (.leaf (2248532000000:ℤ)) (.leaf (1329683100000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 135 (.branch 127 (.leaf (1949556696264458:ℤ)) (.leaf (2226138621407709:ℤ))) (.branch 143 (.leaf (2379064729366125:ℤ)) (.leaf (2549835562568366:ℤ)))) (.branch 178 (.branch 169 (.leaf (2846310998485636:ℤ)) (.leaf (3270102660026147:ℤ))) (.branch 188 (.leaf (3600135403075260:ℤ)) (.branch 200 (.leaf (4035823537510735:ℤ)) (.leaf (4684881018381132:ℤ)))))), (.branch 155 (.branch 135 (.branch 127 (.leaf (1960505027741433:ℤ)) (.leaf (2243727296000870:ℤ))) (.branch 143 (.leaf (2400882469248215:ℤ)) (.leaf (2576814783560087:ℤ)))) (.branch 178 (.branch 169 (.leaf (2883283252704786:ℤ)) (.leaf (3323449831631087:ℤ))) (.branch 188 (.leaf (3667789428882881:ℤ)) (.branch 200 (.leaf (4124261874031185:ℤ)) (.leaf (4807905278255265:ℤ)))))), (.branch 155 (.branch 135 (.branch 127 (.leaf (1958210241935223:ℤ)) (.leaf (2241432309302674:ℤ))) (.branch 143 (.leaf (2398949107324012:ℤ)) (.leaf (2575648651430148:ℤ)))) (.branch 178 (.branch 169 (.leaf (2884489167895927:ℤ)) (.leaf (3330683643241851:ℤ))) (.branch 188 (.leaf (3682144451864202:ℤ)) (.branch 200 (.leaf (4151620074637689:ℤ)) (.leaf (4862951231647052:ℤ)))))), (.branch 155 (.branch 135 (.branch 127 (.leaf (1969622519887312:ℤ)) (.leaf (2259878479627557:ℤ))) (.branch 143 (.leaf (2421908932379322:ℤ)) (.leaf (2604149761298355:ℤ)))) (.branch 178 (.branch 169 (.leaf (2923811846344917:ℤ)) (.leaf (3387979264478381:ℤ))) (.branch 188 (.leaf (3755365310824312:ℤ)) (.branch 200 (.leaf (4248314780807894:ℤ)) (.leaf (4999524999504733:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 25 21) 8000 (endpointMeanRuns 25 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 25 21, EndpointRunConditions (endpointMeanCutoff 25 21) (endpointMeanBox 25 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 25 21 h) (endpointMeanCornerA 25 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 21, endpointJoint24Q (endpointMeanCornerK 25 21 h) (endpointMeanCornerA 25 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 25 21, endpointRunWeightQ (endpointMeanCutoff 25 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 25 21) = (418594941/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 25 21 h = (logRoundedQ ((endpointMeanCutoff 25 21:ℚ)/200)).2+(418594941/1000000000000000:ℚ)+((endpointMeanRuns 25 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 25 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 25 21) r*endpointJoint24Q (endpointMeanCornerK 25 21 h) (endpointMeanCornerA 25 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 25 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 25 21 h≤endpointMeanCorner 25 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 25 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint25_21

namespace EndpointAnalyticJoint25_22
private noncomputable def weights : IntegerLookupTree := (.branch 1170 (.branch 807 (.leaf (32953573300000:ℤ)) (.branch 917 (.leaf (12997072500000:ℤ)) (.leaf (24480196200000:ℤ)))) (.branch 1877 (.branch 1468 (.leaf (16628506100000:ℤ)) (.leaf (11196084900000:ℤ))) (.branch 2989 (.leaf (8928278900000:ℤ)) (.leaf (1324025900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 127 (.leaf (1960505027741433:ℤ)) (.branch 143 (.leaf (2243727296000870:ℤ)) (.leaf (2576814783560087:ℤ)))) (.branch 188 (.branch 169 (.leaf (2883283252704786:ℤ)) (.leaf (3323449831631087:ℤ))) (.branch 200 (.leaf (4124261874031185:ℤ)) (.leaf (4807905278255265:ℤ))))), (.branch 155 (.branch 127 (.leaf (1971514842919986:ℤ)) (.branch 143 (.leaf (2261454938343370:ℤ)) (.leaf (2604079465456033:ℤ)))) (.branch 188 (.branch 169 (.leaf (2920735759286648:ℤ)) (.leaf (3377667288060126:ℤ))) (.branch 200 (.leaf (4214638189081616:ℤ)) (.leaf (4934160136400347:ℤ))))), (.branch 155 (.branch 127 (.leaf (1969622519887312:ℤ)) (.branch 143 (.leaf (2259878479627557:ℤ)) (.leaf (2604149761298355:ℤ)))) (.branch 188 (.branch 169 (.leaf (2923811846344917:ℤ)) (.leaf (3387979264478381:ℤ))) (.branch 200 (.leaf (4248314780807894:ℤ)) (.leaf (4999524999504733:ℤ))))), (.branch 155 (.branch 127 (.leaf (1981101307596755:ℤ)) (.branch 143 (.leaf (2278476455205828:ℤ)) (.leaf (2632966253182375:ℤ)))) (.branch 188 (.branch 169 (.leaf (2963670589570156:ℤ)) (.leaf (3446260505654988:ℤ))) (.branch 200 (.leaf (4347261587611885:ℤ)) (.leaf (5139934379355691:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 25 22) 8000 (endpointMeanRuns 25 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 25 22, EndpointRunConditions (endpointMeanCutoff 25 22) (endpointMeanBox 25 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 25 22 h) (endpointMeanCornerA 25 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 22, endpointJoint24Q (endpointMeanCornerK 25 22 h) (endpointMeanCornerA 25 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 25 22, endpointRunWeightQ (endpointMeanCutoff 25 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 25 22) = (325991/781250000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 25 22 h = (logRoundedQ ((endpointMeanCutoff 25 22:ℚ)/200)).2+(325991/781250000000:ℚ)+((endpointMeanRuns 25 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 25 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 25 22) r*endpointJoint24Q (endpointMeanCornerK 25 22 h) (endpointMeanCornerA 25 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 25 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 25 22 h≤endpointMeanCorner 25 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 25 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint25_22

namespace EndpointAnalyticJoint25_23
private noncomputable def weights : IntegerLookupTree := (.branch 1170 (.branch 807 (.leaf (31007430000000:ℤ)) (.branch 1022 (.leaf (25665290700000:ℤ)) (.leaf (11518482900000:ℤ)))) (.branch 1877 (.branch 1468 (.leaf (16519967600000:ℤ)) (.leaf (11131501700000:ℤ))) (.branch 2989 (.leaf (8883185800000:ℤ)) (.leaf (1318433200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 127 (.leaf (1971514842919986:ℤ)) (.branch 143 (.leaf (2261454938343370:ℤ)) (.leaf (2604079465456033:ℤ)))) (.branch 179 (.branch 169 (.leaf (2920735759286648:ℤ)) (.leaf (3377667288060126:ℤ))) (.branch 200 (.leaf (3780437163459644:ℤ)) (.leaf (4934160136400347:ℤ))))), (.branch 155 (.branch 127 (.leaf (1982586487080637:ℤ)) (.branch 143 (.leaf (2279322646416494:ℤ)) (.leaf (2631632628652080:ℤ)))) (.branch 179 (.branch 169 (.leaf (2958674756485742:ℤ)) (.leaf (3432769226798374:ℤ))) (.branch 200 (.leaf (3852590297427043:ℤ)) (.leaf (5063730427833466:ℤ))))), (.branch 155 (.branch 127 (.leaf (1981101307596755:ℤ)) (.branch 143 (.leaf (2278476455205828:ℤ)) (.leaf (2632966253182375:ℤ)))) (.branch 179 (.branch 169 (.leaf (2963670589570156:ℤ)) (.leaf (3446260505654988:ℤ))) (.branch 200 (.leaf (3877055355567538:ℤ)) (.leaf (5139934379355691:ℤ))))), (.branch 155 (.branch 127 (.leaf (1992646992676609:ℤ)) (.branch 143 (.leaf (2297227485339343:ℤ)) (.leaf (2662101616974936:ℤ)))) (.branch 179 (.branch 169 (.leaf (3004072705452392:ℤ)) (.leaf (3505544321761346:ℤ))) (.branch 200 (.leaf (3955390128155171:ℤ)) (.leaf (5284287092613749:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 25 23) 8000 (endpointMeanRuns 25 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 25 23, EndpointRunConditions (endpointMeanCutoff 25 23) (endpointMeanBox 25 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 25 23 h) (endpointMeanCornerA 25 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 25 23, endpointJoint24Q (endpointMeanCornerK 25 23 h) (endpointMeanCornerA 25 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 25 23, endpointRunWeightQ (endpointMeanCutoff 25 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 25 23) = (415957129/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 25 23 h = (logRoundedQ ((endpointMeanCutoff 25 23:ℚ)/200)).2+(415957129/1000000000000000:ℚ)+((endpointMeanRuns 25 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 25 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 25 23) r*endpointJoint24Q (endpointMeanCornerK 25 23 h) (endpointMeanCornerA 25 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 25 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 25 23 h≤endpointMeanCorner 25 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 25 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint25_23

namespace EndpointAnalyticJoint26_07
private noncomputable def weights : IntegerLookupTree := (.branch 1129 (.branch 790 (.leaf (65156430400000:ℤ)) (.leaf (49193695700000:ℤ))) (.branch 1837 (.leaf (44394153800000:ℤ)) (.leaf (29996166500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 170 (.branch 143 (.leaf (1800835757070668:ℤ)) (.leaf (2222615921920911:ℤ))) (.branch 200 (.leaf (2669278700863040:ℤ)) (.leaf (3355569334667818:ℤ)))), (.branch 170 (.branch 143 (.leaf (1804892503202596:ℤ)) (.leaf (2232313810646947:ℤ))) (.branch 200 (.leaf (2687646062005948:ℤ)) (.leaf (3392541139336939:ℤ)))), (.branch 170 (.branch 143 (.leaf (1803768255781172:ℤ)) (.leaf (2231257713408943:ℤ))) (.branch 200 (.leaf (2689108362129283:ℤ)) (.leaf (3407181135952076:ℤ)))), (.branch 170 (.branch 143 (.leaf (1807984648649721:ℤ)) (.leaf (2241445790380790:ℤ))) (.branch 200 (.leaf (2708654977452775:ℤ)) (.leaf (3447458198730704:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 26 7) 8000 (endpointMeanRuns 26 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 26 7, EndpointRunConditions (endpointMeanCutoff 26 7) (endpointMeanBox 26 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 26 7 h) (endpointMeanCornerA 26 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 7, endpointJoint24Q (endpointMeanCornerK 26 7 h) (endpointMeanCornerA 26 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 26 7, endpointRunWeightQ (endpointMeanCutoff 26 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 26 7) = (218027357/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 26 7 h = (logRoundedQ ((endpointMeanCutoff 26 7:ℚ)/200)).2+(218027357/500000000000000:ℚ)+((endpointMeanRuns 26 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 26 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 26 7) r*endpointJoint24Q (endpointMeanCornerK 26 7 h) (endpointMeanCornerA 26 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 26 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 26 7 h≤endpointMeanCorner 26 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 26 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint26_07

namespace EndpointAnalyticJoint26_08
private noncomputable def weights : IntegerLookupTree := (.branch 1129 (.branch 790 (.leaf (62791293200000:ℤ)) (.leaf (48892624700000:ℤ))) (.branch 1837 (.leaf (44175343800000:ℤ)) (.leaf (29877997500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 170 (.branch 143 (.leaf (1804892503202596:ℤ)) (.leaf (2232313810646947:ℤ))) (.branch 200 (.leaf (2687646062005948:ℤ)) (.leaf (3392541139336939:ℤ)))), (.branch 170 (.branch 143 (.leaf (1815187311597286:ℤ)) (.leaf (2257015712881258:ℤ))) (.branch 200 (.leaf (2734637697585704:ℤ)) (.leaf (3487819110252244:ℤ)))), (.branch 170 (.branch 143 (.leaf (1807984648649721:ℤ)) (.leaf (2241445790380790:ℤ))) (.branch 200 (.leaf (2708654977452775:ℤ)) (.leaf (3447458198730704:ℤ)))), (.branch 170 (.branch 143 (.leaf (1818686191363291:ℤ)) (.leaf (2267405524902786:ℤ))) (.branch 200 (.leaf (2758697691804691:ℤ)) (.leaf (3551399873081548:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 26 8) 8000 (endpointMeanRuns 26 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 26 8, EndpointRunConditions (endpointMeanCutoff 26 8) (endpointMeanBox 26 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 26 8 h) (endpointMeanCornerA 26 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 8, endpointJoint24Q (endpointMeanCornerK 26 8 h) (endpointMeanCornerA 26 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 26 8, endpointRunWeightQ (endpointMeanCutoff 26 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 26 8) = (217475499/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 26 8 h = (logRoundedQ ((endpointMeanCutoff 26 8:ℚ)/200)).2+(217475499/500000000000000:ℚ)+((endpointMeanRuns 26 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 26 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 26 8) r*endpointJoint24Q (endpointMeanCornerK 26 8 h) (endpointMeanCornerA 26 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 26 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 26 8 h≤endpointMeanCorner 26 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 26 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint26_08

namespace EndpointAnalyticJoint26_09
private noncomputable def weights : IntegerLookupTree := (.branch 1129 (.branch 790 (.leaf (59593558600000:ℤ)) (.leaf (48475916800000:ℤ))) (.branch 1837 (.leaf (43872492100000:ℤ)) (.leaf (29714441400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 170 (.branch 143 (.leaf (1815187311597286:ℤ)) (.leaf (2257015712881258:ℤ))) (.branch 200 (.leaf (2734637697585704:ℤ)) (.leaf (3487819110252244:ℤ)))), (.branch 170 (.branch 143 (.leaf (1825540839876784:ℤ)) (.leaf (2281990956601467:ℤ))) (.branch 200 (.leaf (2782450949465934:ℤ)) (.leaf (3585772919534400:ℤ)))), (.branch 170 (.branch 143 (.leaf (1818686191363291:ℤ)) (.leaf (2267405524902786:ℤ))) (.branch 200 (.leaf (2758697691804691:ℤ)) (.leaf (3551399873081548:ℤ)))), (.branch 170 (.branch 143 (.leaf (1829451076991047:ℤ)) (.leaf (2293665917071443:ℤ))) (.branch 200 (.leaf (2809664951098854:ℤ)) (.leaf (3658475413325480:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 26 9) 8000 (endpointMeanRuns 26 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 26 9, EndpointRunConditions (endpointMeanCutoff 26 9) (endpointMeanBox 26 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 26 9 h) (endpointMeanCornerA 26 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 9, endpointJoint24Q (endpointMeanCornerK 26 9 h) (endpointMeanCornerA 26 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 26 9, endpointRunWeightQ (endpointMeanCutoff 26 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 26 9) = (216711681/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 26 9 h = (logRoundedQ ((endpointMeanCutoff 26 9:ℚ)/200)).2+(216711681/500000000000000:ℚ)+((endpointMeanRuns 26 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 26 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 26 9) r*endpointJoint24Q (endpointMeanCornerK 26 9 h) (endpointMeanCornerA 26 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 26 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 26 9 h≤endpointMeanCorner 26 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 26 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint26_09

namespace EndpointAnalyticJoint26_10
private noncomputable def weights : IntegerLookupTree := (.branch 1129 (.branch 790 (.leaf (56523349400000:ℤ)) (.leaf (48064666300000:ℤ))) (.branch 1837 (.leaf (43573606700000:ℤ)) (.leaf (29553027300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 170 (.branch 143 (.leaf (1825540839876784:ℤ)) (.leaf (2281990956601467:ℤ))) (.branch 200 (.leaf (2782450949465934:ℤ)) (.leaf (3585772919534400:ℤ)))), (.branch 170 (.branch 143 (.leaf (1835953422969605:ℤ)) (.leaf (2307242566496409:ℤ))) (.branch 200 (.leaf (2831100183040335:ℤ)) (.leaf (3686477716883763:ℤ)))), (.branch 170 (.branch 143 (.leaf (1829451076991047:ℤ)) (.leaf (2293665917071443:ℤ))) (.branch 200 (.leaf (2809664951098854:ℤ)) (.leaf (3658475413325480:ℤ)))), (.branch 170 (.branch 143 (.leaf (1840279680462561:ℤ)) (.leaf (2320230449010989:ℤ))) (.branch 200 (.leaf (2861573836410133:ℤ)) (.leaf (3768779306255184:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 26 10) 8000 (endpointMeanRuns 26 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 26 10, EndpointRunConditions (endpointMeanCutoff 26 10) (endpointMeanBox 26 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 26 10 h) (endpointMeanCornerA 26 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 10, endpointJoint24Q (endpointMeanCornerK 26 10 h) (endpointMeanCornerA 26 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 26 10, endpointRunWeightQ (endpointMeanCutoff 26 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 26 10) = (431915733/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 26 10 h = (logRoundedQ ((endpointMeanCutoff 26 10:ℚ)/200)).2+(431915733/1000000000000000:ℚ)+((endpointMeanRuns 26 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 26 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 26 10) r*endpointJoint24Q (endpointMeanCornerK 26 10 h) (endpointMeanCornerA 26 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 26 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 26 10 h≤endpointMeanCorner 26 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 26 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint26_10

namespace EndpointAnalyticJoint26_11
private noncomputable def weights : IntegerLookupTree := (.branch 1129 (.branch 790 (.leaf (53575531300000:ℤ)) (.leaf (47658732300000:ℤ))) (.branch 1837 (.leaf (43278585100000:ℤ)) (.branch 3038 (.leaf (11240999400000:ℤ)) (.leaf (1320508300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 143 (.branch 126 (.leaf (1835953422969605:ℤ)) (.leaf (2051223294812287:ℤ))) (.branch 170 (.leaf (2307242566496409:ℤ)) (.branch 200 (.leaf (2831100183040335:ℤ)) (.leaf (3686477716883763:ℤ))))), (.branch 143 (.branch 126 (.leaf (1846425397714644:ℤ)) (.leaf (2067780918126015:ℤ))) (.branch 170 (.leaf (2332773600724936:ℤ)) (.branch 200 (.leaf (2880600014871582:ℤ)) (.leaf (3790010762545765:ℤ))))), (.branch 143 (.branch 126 (.leaf (1840279680462561:ℤ)) (.leaf (2058786824458232:ℤ))) (.branch 170 (.leaf (2320230449010989:ℤ)) (.branch 200 (.leaf (2861573836410133:ℤ)) (.leaf (3768779306255184:ℤ))))), (.branch 143 (.branch 126 (.leaf (1851172378926621:ℤ)) (.leaf (2076100037585677:ℤ))) (.branch 170 (.leaf (2347102643174537:ℤ)) (.branch 200 (.leaf (2914441744388231:ℤ)) (.leaf (3882408887462349:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 26 11) 8000 (endpointMeanRuns 26 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 26 11, EndpointRunConditions (endpointMeanCutoff 26 11) (endpointMeanBox 26 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 26 11 h) (endpointMeanCornerA 26 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 11, endpointJoint24Q (endpointMeanCornerK 26 11 h) (endpointMeanCornerA 26 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 26 11, endpointRunWeightQ (endpointMeanCutoff 26 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 26 11) = (215213797/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 26 11 h = (logRoundedQ ((endpointMeanCutoff 26 11:ℚ)/200)).2+(215213797/500000000000000:ℚ)+((endpointMeanRuns 26 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 26 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 26 11) r*endpointJoint24Q (endpointMeanCornerK 26 11 h) (endpointMeanCornerA 26 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 26 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 26 11 h≤endpointMeanCorner 26 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 26 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint26_11

namespace EndpointAnalyticJoint26_12
private noncomputable def weights : IntegerLookupTree := (.branch 1491 (.branch 790 (.leaf (50745192800000:ℤ)) (.branch 1129 (.leaf (47257978900000:ℤ)) (.leaf (23964987800000:ℤ)))) (.branch 1837 (.leaf (10033870400000:ℤ)) (.branch 3038 (.leaf (11180060700000:ℤ)) (.leaf (1314546400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 153 (.branch 126 (.leaf (1846425397714644:ℤ)) (.branch 143 (.leaf (2067780918126015:ℤ)) (.leaf (2332773600724936:ℤ)))) (.branch 170 (.leaf (2514495354920558:ℤ)) (.branch 200 (.leaf (2880600014871582:ℤ)) (.leaf (3790010762545765:ℤ))))), (.branch 153 (.branch 126 (.leaf (1856957102872059:ℤ)) (.branch 143 (.leaf (2084472195776885:ℤ)) (.leaf (2358587151286266:ℤ)))) (.branch 170 (.leaf (2547624798217078:ℤ)) (.branch 200 (.leaf (2930965317082855:ℤ)) (.leaf (3896451486584594:ℤ))))), (.branch 153 (.branch 126 (.leaf (1851172378926621:ℤ)) (.branch 143 (.leaf (2076100037585677:ℤ)) (.leaf (2347102643174537:ℤ)))) (.branch 170 (.leaf (2534169320039289:ℤ)) (.branch 200 (.leaf (2914441744388231:ℤ)) (.leaf (3882408887462349:ℤ))))), (.branch 153 (.branch 126 (.leaf (1862129551764378:ℤ)) (.branch 143 (.leaf (2093558844878211:ℤ)) (.leaf (2374286062811170:ℤ)))) (.branch 170 (.leaf (2569226096654153:ℤ)) (.branch 200 (.leaf (2968286393087957:ℤ)) (.leaf (3999464427229591:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 26 12) 8000 (endpointMeanRuns 26 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 26 12, EndpointRunConditions (endpointMeanCutoff 26 12) (endpointMeanBox 26 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 26 12 h) (endpointMeanCornerA 26 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 12, endpointJoint24Q (endpointMeanCornerK 26 12 h) (endpointMeanCornerA 26 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 26 12, endpointRunWeightQ (endpointMeanCutoff 26 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 26 12) = (214479223/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 26 12 h = (logRoundedQ ((endpointMeanCutoff 26 12:ℚ)/200)).2+(214479223/500000000000000:ℚ)+((endpointMeanRuns 26 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 26 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 26 12) r*endpointJoint24Q (endpointMeanCornerK 26 12 h) (endpointMeanCornerA 26 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 26 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 26 12 h≤endpointMeanCorner 26 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 26 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint26_12

namespace EndpointAnalyticJoint26_13
private noncomputable def weights : IntegerLookupTree := (.branch 1491 (.branch 790 (.leaf (48027634700000:ℤ)) (.branch 1129 (.leaf (46862275700000:ℤ)) (.leaf (23799877400000:ℤ)))) (.branch 1837 (.leaf (9973080800000:ℤ)) (.branch 3038 (.leaf (11119889900000:ℤ)) (.leaf (1308659600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 153 (.branch 126 (.leaf (1856957102872059:ℤ)) (.branch 143 (.leaf (2084472195776885:ℤ)) (.leaf (2358587151286266:ℤ)))) (.branch 170 (.leaf (2547624798217078:ℤ)) (.branch 200 (.leaf (2930965317082855:ℤ)) (.leaf (3896451486584594:ℤ))))), (.branch 153 (.branch 126 (.leaf (1867548879134246:ℤ)) (.branch 143 (.leaf (2101298206632409:ℤ)) (.leaf (2384686344394466:ℤ)))) (.branch 170 (.leaf (2581190734669562:ℤ)) (.branch 200 (.leaf (2982211221826154:ℤ)) (.leaf (4005881549821581:ℤ))))), (.branch 153 (.branch 126 (.leaf (1862129551764378:ℤ)) (.branch 143 (.leaf (2093558844878211:ℤ)) (.leaf (2374286062811170:ℤ)))) (.branch 170 (.leaf (2569226096654153:ℤ)) (.branch 200 (.leaf (2968286393087957:ℤ)) (.leaf (3999464427229591:ℤ))))), (.branch 153 (.branch 126 (.leaf (1873151580602559:ℤ)) (.branch 143 (.leaf (2111164470699023:ℤ)) (.leaf (2401784312438427:ℤ)))) (.branch 170 (.leaf (2604767835965437:ℤ)) (.branch 200 (.leaf (3023125827907253:ℤ)) (.leaf (4120049219012106:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 26 13) 8000 (endpointMeanRuns 26 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 26 13, EndpointRunConditions (endpointMeanCutoff 26 13) (endpointMeanBox 26 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 26 13 h) (endpointMeanCornerA 26 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 13, endpointJoint24Q (endpointMeanCornerK 26 13 h) (endpointMeanCornerA 26 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 26 13, endpointRunWeightQ (endpointMeanCutoff 26 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 26 13) = (427507813/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 26 13 h = (logRoundedQ ((endpointMeanCutoff 26 13:ℚ)/200)).2+(427507813/1000000000000000:ℚ)+((endpointMeanRuns 26 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 26 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 26 13) r*endpointJoint24Q (endpointMeanCornerK 26 13 h) (endpointMeanCornerA 26 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 26 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 26 13 h≤endpointMeanCorner 26 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 26 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint26_13

namespace EndpointAnalyticJoint26_14
private noncomputable def weights : IntegerLookupTree := (.branch 1129 (.branch 790 (.leaf (45418359000000:ℤ)) (.branch 919 (.leaf (17350154100000:ℤ)) (.leaf (22110562500000:ℤ)))) (.branch 1837 (.branch 1491 (.leaf (23636821800000:ℤ)) (.leaf (9913047600000:ℤ))) (.branch 3038 (.leaf (11060467900000:ℤ)) (.leaf (1302846100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 153 (.branch 126 (.leaf (1867548879134246:ℤ)) (.branch 143 (.leaf (2101298206632409:ℤ)) (.leaf (2384686344394466:ℤ)))) (.branch 186 (.branch 170 (.leaf (2581190734669562:ℤ)) (.leaf (2982211221826154:ℤ))) (.branch 200 (.leaf (3464170892346796:ℤ)) (.leaf (4005881549821581:ℤ))))), (.branch 153 (.branch 126 (.leaf (1878201069136860:ℤ)) (.branch 143 (.leaf (2118260038268792:ℤ)) (.leaf (2411074340857052:ℤ)))) (.branch 186 (.branch 170 (.leaf (2615198915243208:ℤ)) (.leaf (3034353125828689:ℤ))) (.branch 200 (.leaf (3542358847691052:ℤ)) (.leaf (4118384906484978:ℤ))))), (.branch 153 (.branch 126 (.leaf (1873151580602559:ℤ)) (.branch 143 (.leaf (2111164470699023:ℤ)) (.leaf (2401784312438427:ℤ)))) (.branch 186 (.branch 170 (.leaf (2604767835965437:ℤ)) (.leaf (3023125827907253:ℤ))) (.branch 200 (.leaf (3534016759611583:ℤ)) (.leaf (4120049219012106:ℤ))))), (.branch 153 (.branch 126 (.leaf (1884238849326763:ℤ)) (.branch 143 (.leaf (2128918149707495:ℤ)) (.leaf (2429601038320257:ℤ)))) (.branch 186 (.branch 170 (.leaf (2640801246770678:ℤ)) (.leaf (3078978427634858:ℤ))) (.branch 200 (.leaf (3618937526265448:ℤ)) (.leaf (4244269670587030:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 26 14) 8000 (endpointMeanRuns 26 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 26 14, EndpointRunConditions (endpointMeanCutoff 26 14) (endpointMeanBox 26 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 26 14 h) (endpointMeanCornerA 26 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 14, endpointJoint24Q (endpointMeanCornerK 26 14 h) (endpointMeanCornerA 26 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 26 14, endpointRunWeightQ (endpointMeanCutoff 26 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 26 14) = (13314851/31250000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 26 14 h = (logRoundedQ ((endpointMeanCutoff 26 14:ℚ)/200)).2+(13314851/31250000000000:ℚ)+((endpointMeanRuns 26 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 26 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 26 14) r*endpointJoint24Q (endpointMeanCornerK 26 14 h) (endpointMeanCornerA 26 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 26 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 26 14 h≤endpointMeanCorner 26 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 26 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint26_14

namespace EndpointAnalyticJoint26_15
private noncomputable def weights : IntegerLookupTree := (.branch 1235 (.branch 888 (.branch 790 (.leaf (42913059900000:ℤ)) (.leaf (12966685700000:ℤ))) (.branch 1068 (.leaf (20020801300000:ℤ)) (.leaf (12850465400000:ℤ)))) (.branch 1837 (.branch 1491 (.leaf (13455049200000:ℤ)) (.leaf (9853752400000:ℤ))) (.branch 3038 (.leaf (11001776300000:ℤ)) (.leaf (1297104000000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 143 (.branch 126 (.leaf (1878201069136860:ℤ)) (.leaf (2118260038268792:ℤ))) (.branch 153 (.leaf (2411074340857052:ℤ)) (.leaf (2615198915243208:ℤ)))) (.branch 189 (.branch 174 (.leaf (2874474739826840:ℤ)) (.leaf (3149354913076762:ℤ))) (.branch 200 (.leaf (3653735664940124:ℤ)) (.leaf (4118384906484978:ℤ))))), (.branch 164 (.branch 143 (.branch 126 (.leaf (1888914017469878:ℤ)) (.leaf (2135358787041235:ℤ))) (.branch 153 (.leaf (2437754336457780:ℤ)) (.leaf (2649655166674380:ℤ)))) (.branch 189 (.branch 174 (.leaf (2920032137632816:ℤ)) (.leaf (3208095584380627:ℤ))) (.branch 200 (.leaf (3740178939207043:ℤ)) (.leaf (4234047868619263:ℤ))))), (.branch 164 (.branch 143 (.branch 126 (.leaf (1884238849326763:ℤ)) (.leaf (2128918149707495:ℤ))) (.branch 153 (.leaf (2429601038320257:ℤ)) (.leaf (2640801246770678:ℤ)))) (.branch 189 (.branch 174 (.leaf (2911101092733412:ℤ)) (.leaf (3200325553347926:ℤ))) (.branch 200 (.leaf (3738722639194575:ℤ)) (.leaf (4244269670587030:ℤ))))), (.branch 164 (.branch 143 (.branch 126 (.leaf (1895391744094814:ℤ)) (.leaf (2146821126945788:ℤ))) (.branch 153 (.leaf (2457739928950506:ℤ)) (.leaf (2677333130674500:ℤ)))) (.branch 189 (.branch 174 (.leaf (2959736225812371:ℤ)) (.leaf (3263508061820589:ℤ))) (.branch 200 (.leaf (3833047889361386:ℤ)) (.leaf (4372235397950956:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 26 15) 8000 (endpointMeanRuns 26 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 26 15, EndpointRunConditions (endpointMeanCutoff 26 15) (endpointMeanBox 26 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 26 15 h) (endpointMeanCornerA 26 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 15, endpointJoint24Q (endpointMeanCornerK 26 15 h) (endpointMeanCornerA 26 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 26 15, endpointRunWeightQ (endpointMeanCutoff 26 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 26 15) = (21233013/50000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 26 15 h = (logRoundedQ ((endpointMeanCutoff 26 15:ℚ)/200)).2+(21233013/50000000000000:ℚ)+((endpointMeanRuns 26 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 26 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 26 15) r*endpointJoint24Q (endpointMeanCornerK 26 15 h) (endpointMeanCornerA 26 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 26 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 26 15 h≤endpointMeanCorner 26 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 26 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint26_15

namespace EndpointAnalyticJoint26_16
private noncomputable def weights : IntegerLookupTree := (.branch 1235 (.branch 888 (.branch 790 (.leaf (40507614400000:ℤ)) (.leaf (12852197100000:ℤ))) (.branch 1068 (.leaf (19860899000000:ℤ)) (.leaf (12758027000000:ℤ)))) (.branch 1837 (.branch 1491 (.leaf (13366699300000:ℤ)) (.leaf (9795177100000:ℤ))) (.branch 2323 (.leaf (5738561700000:ℤ)) (.branch 3038 (.leaf (2346251300000:ℤ)) (.leaf (1291431600000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 153 (.branch 134 (.branch 126 (.leaf (1888914017469878:ℤ)) (.leaf (2135358787041235:ℤ))) (.branch 143 (.leaf (2269634926074554:ℤ)) (.leaf (2437754336457780:ℤ)))) (.branch 174 (.branch 164 (.leaf (2649655166674380:ℤ)) (.leaf (2920032137632816:ℤ))) (.branch 189 (.leaf (3208095584380627:ℤ)) (.branch 200 (.leaf (3740178939207043:ℤ)) (.leaf (4234047868619263:ℤ)))))), (.branch 153 (.branch 134 (.branch 126 (.leaf (1899688070688774:ℤ)) (.leaf (2152595558154797:ℤ))) (.branch 143 (.leaf (2290958250652173:ℤ)) (.leaf (2464729562343695:ℤ)))) (.branch 174 (.branch 164 (.leaf (2684565392468948:ℤ)) (.leaf (2966311572222103:ℤ))) (.branch 189 (.leaf (3267931866233467:ℤ)) (.branch 200 (.leaf (3828667364068105:ℤ)) (.leaf (4352959172303311:ℤ)))))), (.branch 153 (.branch 134 (.branch 126 (.leaf (1895391744094814:ℤ)) (.leaf (2146821126945788:ℤ))) (.branch 143 (.leaf (2284539447130980:ℤ)) (.leaf (2457739928950506:ℤ)))) (.branch 174 (.branch 164 (.leaf (2677333130674500:ℤ)) (.leaf (2959736225812371:ℤ))) (.branch 189 (.leaf (3263508061820589:ℤ)) (.branch 200 (.leaf (3833047889361386:ℤ)) (.leaf (4372235397950956:ℤ)))))), (.branch 153 (.branch 134 (.branch 126 (.leaf (1906610653350227:ℤ)) (.leaf (2164874657926152:ℤ))) (.branch 143 (.leaf (2306946358366619:ℤ)) (.leaf (2486204715542035:ℤ)))) (.branch 174 (.branch 164 (.leaf (2714370383372427:ℤ)) (.leaf (3009183895486337:ℤ))) (.branch 189 (.leaf (3327937952570576:ℤ)) (.branch 200 (.leaf (3929752896915325:ℤ)) (.leaf (4504059322048532:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 26 16) 8000 (endpointMeanRuns 26 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 26 16, EndpointRunConditions (endpointMeanCutoff 26 16) (endpointMeanBox 26 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 26 16 h) (endpointMeanCornerA 26 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 16, endpointJoint24Q (endpointMeanCornerK 26 16 h) (endpointMeanCornerA 26 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 26 16, endpointRunWeightQ (endpointMeanCutoff 26 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 26 16) = (42326247/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 26 16 h = (logRoundedQ ((endpointMeanCutoff 26 16:ℚ)/200)).2+(42326247/100000000000000:ℚ)+((endpointMeanRuns 26 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 26 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 26 16) r*endpointJoint24Q (endpointMeanCornerK 26 16 h) (endpointMeanCornerA 26 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 26 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 26 16 h≤endpointMeanCorner 26 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 26 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint26_16

namespace EndpointAnalyticJoint26_17
private noncomputable def weights : IntegerLookupTree := (.branch 1235 (.branch 888 (.branch 790 (.leaf (38198073400000:ℤ)) (.leaf (12739081900000:ℤ))) (.branch 1068 (.leaf (19702915000000:ℤ)) (.leaf (12666697600000:ℤ)))) (.branch 1837 (.branch 1491 (.leaf (13279409300000:ℤ)) (.leaf (9737304600000:ℤ))) (.branch 2323 (.leaf (5707877900000:ℤ)) (.branch 3038 (.leaf (2334903700000:ℤ)) (.leaf (1285827300000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 153 (.branch 134 (.branch 126 (.leaf (1899688070688774:ℤ)) (.leaf (2152595558154797:ℤ))) (.branch 143 (.leaf (2290958250652173:ℤ)) (.leaf (2464729562343695:ℤ)))) (.branch 174 (.branch 164 (.leaf (2684565392468948:ℤ)) (.leaf (2966311572222103:ℤ))) (.branch 189 (.leaf (3267931866233467:ℤ)) (.branch 200 (.leaf (3828667364068105:ℤ)) (.leaf (4352959172303311:ℤ)))))), (.branch 153 (.branch 134 (.branch 126 (.leaf (1910523577325718:ℤ)) (.leaf (2169971465735833:ℤ))) (.branch 143 (.leaf (2312481908845491:ℤ)) (.leaf (2492003285416434:ℤ)))) (.branch 174 (.branch 164 (.leaf (2719935573913725:ℤ)) (.leaf (3013324487117407:ℤ))) (.branch 189 (.leaf (3328884193581772:ℤ)) (.branch 200 (.leaf (3919249325484949:ℤ)) (.leaf (4475210045728329:ℤ)))))), (.branch 153 (.branch 134 (.branch 126 (.leaf (1906610653350227:ℤ)) (.leaf (2164874657926152:ℤ))) (.branch 143 (.leaf (2306946358366619:ℤ)) (.leaf (2486204715542035:ℤ)))) (.branch 174 (.branch 164 (.leaf (2714370383372427:ℤ)) (.leaf (3009183895486337:ℤ))) (.branch 189 (.leaf (3327937952570576:ℤ)) (.branch 200 (.leaf (3929752896915325:ℤ)) (.leaf (4504059322048532:ℤ)))))), (.branch 153 (.branch 134 (.branch 126 (.leaf (1917895967835733:ℤ)) (.leaf (2183080008718964:ℤ))) (.branch 143 (.leaf (2329573038042559:ℤ)) (.leaf (2514999172521448:ℤ)))) (.branch 174 (.branch 164 (.leaf (2751919995952547:ℤ)) (.leaf (3059457676627554:ℤ))) (.branch 189 (.leaf (3393639852074155:ℤ)) (.branch 200 (.leaf (4028897701402655:ℤ)) (.leaf (4639857768417397:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 26 17) 8000 (endpointMeanRuns 26 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 26 17, EndpointRunConditions (endpointMeanCutoff 26 17) (endpointMeanBox 26 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 26 17 h) (endpointMeanCornerA 26 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 17, endpointJoint24Q (endpointMeanCornerK 26 17 h) (endpointMeanCornerA 26 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 26 17, endpointRunWeightQ (endpointMeanCutoff 26 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 26 17) = (421881449/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 26 17 h = (logRoundedQ ((endpointMeanCutoff 26 17:ℚ)/200)).2+(421881449/1000000000000000:ℚ)+((endpointMeanRuns 26 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 26 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 26 17) r*endpointJoint24Q (endpointMeanCornerK 26 17 h) (endpointMeanCornerA 26 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 26 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 26 17 h≤endpointMeanCorner 26 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 26 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint26_17

namespace EndpointAnalyticJoint26_18
private noncomputable def weights : IntegerLookupTree := (.branch 1235 (.branch 888 (.branch 790 (.leaf (35980654100000:ℤ)) (.leaf (12627307700000:ℤ))) (.branch 1068 (.leaf (19546803800000:ℤ)) (.leaf (12576450900000:ℤ)))) (.branch 1837 (.branch 1491 (.leaf (13193154200000:ℤ)) (.leaf (9680118100000:ℤ))) (.branch 2323 (.leaf (5677557900000:ℤ)) (.branch 3038 (.leaf (2323690500000:ℤ)) (.leaf (1280289500000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 153 (.branch 134 (.branch 126 (.leaf (1910523577325718:ℤ)) (.leaf (2169971465735833:ℤ))) (.branch 143 (.leaf (2312481908845491:ℤ)) (.leaf (2492003285416434:ℤ)))) (.branch 174 (.branch 164 (.leaf (2719935573913725:ℤ)) (.leaf (3013324487117407:ℤ))) (.branch 189 (.leaf (3328884193581772:ℤ)) (.branch 200 (.leaf (3919249325484949:ℤ)) (.leaf (4475210045728329:ℤ)))))), (.branch 153 (.branch 134 (.branch 126 (.leaf (1921420887900834:ℤ)) (.leaf (2187487632904015:ℤ))) (.branch 143 (.leaf (2334207782798036:ℤ)) (.leaf (2519578808727872:ℤ)))) (.branch 174 (.branch 164 (.leaf (2755771771101293:ℤ)) (.leaf (3061082507209235:ℤ))) (.branch 189 (.leaf (3390973382517543:ℤ)) (.branch 200 (.leaf (4011974354176616:ℤ)) (.leaf (4600894279187657:ℤ)))))), (.branch 153 (.branch 134 (.branch 126 (.leaf (1917895967835733:ℤ)) (.leaf (2183080008718964:ℤ))) (.branch 143 (.leaf (2329573038042559:ℤ)) (.leaf (2514999172521448:ℤ)))) (.branch 174 (.branch 164 (.leaf (2751919995952547:ℤ)) (.leaf (3059457676627554:ℤ))) (.branch 189 (.leaf (3393639852074155:ℤ)) (.branch 200 (.leaf (4028897701402655:ℤ)) (.leaf (4639857768417397:ℤ)))))), (.branch 153 (.branch 134 (.branch 126 (.leaf (1929248080606886:ℤ)) (.leaf (2201438456041536:ℤ))) (.branch 143 (.leaf (2352421641661947:ℤ)) (.leaf (2544127118029603:ℤ)))) (.branch 174 (.branch 164 (.leaf (2789989056215098:ℤ)) (.leaf (3110571370900712:ℤ))) (.branch 189 (.leaf (3460638872996431:ℤ)) (.branch 200 (.leaf (4130543857123686:ℤ)) (.leaf (4779750569837477:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 26 18) 8000 (endpointMeanRuns 26 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 26 18, EndpointRunConditions (endpointMeanCutoff 26 18) (endpointMeanBox 26 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 26 18 h) (endpointMeanCornerA 26 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 18, endpointJoint24Q (endpointMeanCornerK 26 18 h) (endpointMeanCornerA 26 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 26 18, endpointRunWeightQ (endpointMeanCutoff 26 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 26 18) = (420516799/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 26 18 h = (logRoundedQ ((endpointMeanCutoff 26 18:ℚ)/200)).2+(420516799/1000000000000000:ℚ)+((endpointMeanRuns 26 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 26 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 26 18) r*endpointJoint24Q (endpointMeanCornerK 26 18 h) (endpointMeanCornerA 26 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 26 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 26 18 h≤endpointMeanCorner 26 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 26 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint26_18

namespace EndpointAnalyticJoint26_19
private noncomputable def weights : IntegerLookupTree := (.branch 1235 (.branch 888 (.branch 790 (.leaf (33851731600000:ℤ)) (.leaf (12516843000000:ℤ))) (.branch 1068 (.leaf (19392521600000:ℤ)) (.leaf (12487261500000:ℤ)))) (.branch 1837 (.branch 1491 (.leaf (13107909600000:ℤ)) (.leaf (9623601600000:ℤ))) (.branch 2323 (.leaf (5647593100000:ℤ)) (.branch 3038 (.leaf (2312608800000:ℤ)) (.leaf (1274816500000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 153 (.branch 134 (.branch 126 (.leaf (1921420887900834:ℤ)) (.leaf (2187487632904015:ℤ))) (.branch 143 (.leaf (2334207782798036:ℤ)) (.leaf (2519578808727872:ℤ)))) (.branch 174 (.branch 164 (.leaf (2755771771101293:ℤ)) (.leaf (3061082507209235:ℤ))) (.branch 189 (.leaf (3390973382517543:ℤ)) (.branch 200 (.leaf (4011974354176616:ℤ)) (.leaf (4600894279187657:ℤ)))))), (.branch 153 (.branch 134 (.branch 126 (.leaf (1932380354933576:ℤ)) (.leaf (2205145191844899:ℤ))) (.branch 143 (.leaf (2356137772336179:ℤ)) (.leaf (2547459471880157:ℤ)))) (.branch 174 (.branch 164 (.leaf (2792080123968273:ℤ)) (.leaf (3109597441630348:ℤ))) (.branch 189 (.leaf (3454220637387284:ℤ)) (.branch 200 (.leaf (4106893152703224:ℤ)) (.leaf (4730108297032268:ℤ)))))), (.branch 153 (.branch 134 (.branch 126 (.leaf (1929248080606886:ℤ)) (.leaf (2201438456041536:ℤ))) (.branch 143 (.leaf (2352421641661947:ℤ)) (.leaf (2544127118029603:ℤ)))) (.branch 174 (.branch 164 (.leaf (2789989056215098:ℤ)) (.leaf (3110571370900712:ℤ))) (.branch 189 (.leaf (3460638872996431:ℤ)) (.branch 200 (.leaf (4130543857123686:ℤ)) (.leaf (4779750569837477:ℤ)))))), (.branch 153 (.branch 134 (.branch 126 (.leaf (1940667387045747:ℤ)) (.leaf (2219951287347630:ℤ))) (.branch 143 (.leaf (2375494345869222:ℤ)) (.leaf (2573592414427893:ℤ)))) (.branch 174 (.branch 164 (.leaf (2828584750010384:ℤ)) (.leaf (3162539010551901:ℤ))) (.branch 189 (.leaf (3528960623789939:ℤ)) (.branch 200 (.leaf (4234754471348901:ℤ)) (.leaf (4923861172075156:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 26 19) 8000 (endpointMeanRuns 26 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 26 19, EndpointRunConditions (endpointMeanCutoff 26 19) (endpointMeanBox 26 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 26 19 h) (endpointMeanCornerA 26 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 19, endpointJoint24Q (endpointMeanCornerK 26 19 h) (endpointMeanCornerA 26 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 26 19, endpointRunWeightQ (endpointMeanCutoff 26 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 26 19) = (419168137/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 26 19 h = (logRoundedQ ((endpointMeanCutoff 26 19:ℚ)/200)).2+(419168137/1000000000000000:ℚ)+((endpointMeanRuns 26 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 26 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 26 19) r*endpointJoint24Q (endpointMeanCornerK 26 19 h) (endpointMeanCornerA 26 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 26 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 26 19 h≤endpointMeanCorner 26 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 26 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint26_19

namespace EndpointAnalyticJoint26_20
private noncomputable def weights : IntegerLookupTree := (.branch 1317 (.branch 930 (.branch 790 (.leaf (31807832100000:ℤ)) (.leaf (17906676900000:ℤ))) (.branch 1129 (.leaf (19565690400000:ℤ)) (.leaf (12238687000000:ℤ)))) (.branch 1837 (.branch 1491 (.leaf (7568770300000:ℤ)) (.leaf (9567739600000:ℤ))) (.branch 2323 (.leaf (5617975300000:ℤ)) (.branch 3038 (.leaf (2301655300000:ℤ)) (.leaf (1269406900000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 153 (.branch 134 (.branch 126 (.leaf (1932380354933576:ℤ)) (.leaf (2205145191844899:ℤ))) (.branch 143 (.leaf (2356137772336179:ℤ)) (.leaf (2547459471880157:ℤ)))) (.branch 170 (.branch 160 (.leaf (2792080123968273:ℤ)) (.leaf (2987485509955066:ℤ))) (.branch 185 (.leaf (3309060630159032:ℤ)) (.branch 200 (.leaf (3913744304132959:ℤ)) (.leaf (4730108297032268:ℤ)))))), (.branch 153 (.branch 134 (.branch 126 (.leaf (1943402332954095:ℤ)) (.leaf (2222945283883139:ℤ))) (.branch 143 (.leaf (2378273795135233:ℤ)) (.leaf (2575648651430148:ℤ)))) (.branch 170 (.branch 160 (.leaf (2828866853347322:ℤ)) (.leaf (3031791413435882:ℤ))) (.branch 185 (.leaf (3366917270377382:ℤ)) (.branch 200 (.leaf (4000699677607738:ℤ)) (.leaf (4862951231647052:ℤ)))))), (.branch 153 (.branch 134 (.branch 126 (.leaf (1940667387045747:ℤ)) (.leaf (2219951287347630:ℤ))) (.branch 143 (.leaf (2375494345869222:ℤ)) (.leaf (2573592414427893:ℤ)))) (.branch 170 (.branch 160 (.leaf (2828584750010384:ℤ)) (.leaf (3033699719663910:ℤ))) (.branch 185 (.leaf (3374106280584509:ℤ)) (.branch 200 (.leaf (4024229661276257:ℤ)) (.leaf (4923861172075156:ℤ)))))), (.branch 153 (.branch 134 (.branch 126 (.leaf (1952154284874673:ℤ)) (.leaf (2238619800917757:ℤ))) (.branch 143 (.leaf (2398793348657502:ℤ)) (.leaf (2603398968810376:ℤ)))) (.branch 170 (.branch 160 (.leaf (2867714362595149:ℤ)) (.leaf (3081054934293236:ℤ))) (.branch 185 (.leaf (3436443284816431:ℤ)) (.branch 200 (.leaf (4119369753683921:ℤ)) (.leaf (5072316742815655:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 26 20) 8000 (endpointMeanRuns 26 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 26 20, EndpointRunConditions (endpointMeanCutoff 26 20) (endpointMeanBox 26 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 26 20 h) (endpointMeanCornerA 26 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 20, endpointJoint24Q (endpointMeanCornerK 26 20 h) (endpointMeanCornerA 26 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 26 20, endpointRunWeightQ (endpointMeanCutoff 26 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 26 20) = (417835093/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 26 20 h = (logRoundedQ ((endpointMeanCutoff 26 20:ℚ)/200)).2+(417835093/1000000000000000:ℚ)+((endpointMeanRuns 26 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 26 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 26 20) r*endpointJoint24Q (endpointMeanCornerK 26 20 h) (endpointMeanCornerA 26 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 26 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 26 20 h≤endpointMeanCorner 26 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 26 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint26_20

namespace EndpointAnalyticJoint26_21
private noncomputable def weights : IntegerLookupTree := (.branch 1317 (.branch 930 (.branch 790 (.leaf (29571791500000:ℤ)) (.leaf (17731448100000:ℤ))) (.branch 1129 (.leaf (19396381500000:ℤ)) (.leaf (12143883000000:ℤ)))) (.branch 1837 (.branch 1491 (.leaf (7514667500000:ℤ)) (.leaf (9504679500000:ℤ))) (.branch 3038 (.leaf (10656257200000:ℤ)) (.leaf (1263300200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 160 (.branch 143 (.branch 126 (.leaf (1943402332954095:ℤ)) (.leaf (2222945283883139:ℤ))) (.branch 153 (.leaf (2575648651430148:ℤ)) (.leaf (2828866853347322:ℤ)))) (.branch 185 (.branch 170 (.leaf (3031791413435882:ℤ)) (.leaf (3366917270377382:ℤ))) (.branch 200 (.leaf (4000699677607738:ℤ)) (.leaf (4862951231647052:ℤ))))), (.branch 160 (.branch 143 (.branch 126 (.leaf (1954487178514734:ℤ)) (.leaf (2240889059556249:ℤ))) (.branch 153 (.leaf (2604149761298355:ℤ)) (.leaf (2866138262032956:ℤ)))) (.branch 185 (.branch 170 (.leaf (3076754395612713:ℤ)) (.leaf (3425785494000051:ℤ))) (.branch 200 (.leaf (4089587021182898:ℤ)) (.leaf (4999524999504733:ℤ))))), (.branch 160 (.branch 143 (.branch 126 (.leaf (1952154284874673:ℤ)) (.leaf (2238619800917757:ℤ))) (.branch 153 (.leaf (2603398968810376:ℤ)) (.leaf (2867714362595149:ℤ)))) (.branch 185 (.branch 170 (.leaf (3081054934293236:ℤ)) (.leaf (3436443284816431:ℤ))) (.branch 200 (.leaf (4119369753683921:ℤ)) (.leaf (5072316742815655:ℤ))))), (.branch 160 (.branch 143 (.branch 126 (.leaf (1963709174170150:ℤ)) (.leaf (2257445305950222:ℤ))) (.branch 153 (.leaf (2633550733521880:ℤ)) (.leaf (2907385280007711:ℤ)))) (.branch 185 (.branch 170 (.leaf (3129149350742063:ℤ)) (.leaf (3499931972419734:ℤ))) (.branch 200 (.leaf (4216759130537353:ℤ)) (.leaf (5225248283879785:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 26 21) 8000 (endpointMeanRuns 26 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 26 21, EndpointRunConditions (endpointMeanCutoff 26 21) (endpointMeanBox 26 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 26 21 h) (endpointMeanCornerA 26 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 21, endpointJoint24Q (endpointMeanCornerK 26 21 h) (endpointMeanCornerA 26 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 26 21, endpointRunWeightQ (endpointMeanCutoff 26 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 26 21) = (416330279/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 26 21 h = (logRoundedQ ((endpointMeanCutoff 26 21:ℚ)/200)).2+(416330279/1000000000000000:ℚ)+((endpointMeanRuns 26 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 26 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 26 21) r*endpointJoint24Q (endpointMeanCornerK 26 21 h) (endpointMeanCornerA 26 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 26 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 26 21 h≤endpointMeanCorner 26 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 26 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint26_21

namespace EndpointAnalyticJoint26_22
private noncomputable def weights : IntegerLookupTree := (.branch 1129 (.branch 790 (.leaf (27699047200000:ℤ)) (.branch 930 (.leaf (17579979700000:ℤ)) (.leaf (19250030300000:ℤ)))) (.branch 1837 (.branch 1491 (.leaf (22379603900000:ℤ)) (.leaf (9450170100000:ℤ))) (.branch 3038 (.leaf (10602302700000:ℤ)) (.leaf (1258021600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 153 (.branch 126 (.leaf (1954487178514734:ℤ)) (.branch 143 (.leaf (2240889059556249:ℤ)) (.leaf (2604149761298355:ℤ)))) (.branch 185 (.branch 170 (.leaf (2866138262032956:ℤ)) (.leaf (3425785494000051:ℤ))) (.branch 200 (.leaf (4089587021182898:ℤ)) (.leaf (4999524999504733:ℤ))))), (.branch 153 (.branch 126 (.leaf (1965635250201540:ℤ)) (.branch 143 (.leaf (2258977678688949:ℤ)) (.leaf (2632966253182375:ℤ)))) (.branch 185 (.branch 170 (.leaf (2903900735861426:ℤ)) (.leaf (3485682987864370:ℤ))) (.branch 200 (.leaf (4180449259272660:ℤ)) (.leaf (5139934379355691:ℤ))))), (.branch 153 (.branch 126 (.leaf (1963709174170150:ℤ)) (.branch 143 (.leaf (2257445305950222:ℤ)) (.leaf (2633550733521880:ℤ)))) (.branch 185 (.branch 170 (.leaf (2907385280007711:ℤ)) (.leaf (3499931972419734:ℤ))) (.branch 200 (.leaf (4216759130537353:ℤ)) (.leaf (5225248283879785:ℤ))))), (.branch 153 (.branch 126 (.leaf (1975332457376733:ℤ)) (.branch 143 (.leaf (2276429122652935:ℤ)) (.leaf (2664051706682078:ℤ)))) (.branch 185 (.branch 170 (.leaf (2947604990462181:ℤ)) (.leaf (3564593620878054:ℤ))) (.branch 200 (.leaf (4316450969002894:ℤ)) (.leaf (5382790746824023:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 26 22) 8000 (endpointMeanRuns 26 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 26 22, EndpointRunConditions (endpointMeanCutoff 26 22) (endpointMeanBox 26 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 26 22 h) (endpointMeanCornerA 26 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 22, endpointJoint24Q (endpointMeanCornerK 26 22 h) (endpointMeanCornerA 26 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 26 22, endpointRunWeightQ (endpointMeanCutoff 26 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 26 22) = (415029513/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 26 22 h = (logRoundedQ ((endpointMeanCutoff 26 22:ℚ)/200)).2+(415029513/1000000000000000:ℚ)+((endpointMeanRuns 26 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 26 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 26 22) r*endpointJoint24Q (endpointMeanCornerK 26 22 h) (endpointMeanCornerA 26 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 26 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 26 22 h≤endpointMeanCorner 26 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 26 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint26_22

namespace EndpointAnalyticJoint26_23
private noncomputable def weights : IntegerLookupTree := (.branch 1491 (.branch 930 (.leaf (51132600200000:ℤ)) (.branch 1129 (.leaf (19105314300000:ℤ)) (.leaf (22233205600000:ℤ)))) (.branch 1837 (.leaf (9396269700000:ℤ)) (.branch 3038 (.leaf (10548951100000:ℤ)) (.leaf (1252802000000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 153 (.branch 126 (.leaf (1965635250201540:ℤ)) (.branch 143 (.leaf (2258977678688949:ℤ)) (.leaf (2632966253182375:ℤ)))) (.branch 170 (.leaf (2903900735861426:ℤ)) (.branch 185 (.leaf (3485682987864370:ℤ)) (.leaf (4180449259272660:ℤ))))), (.branch 153 (.branch 126 (.leaf (1976846908645889:ℤ)) (.branch 143 (.leaf (2277212310468167:ℤ)) (.leaf (2662101616974936:ℤ)))) (.branch 170 (.leaf (2942160744804841:ℤ)) (.branch 185 (.leaf (3546627748049798:ℤ)) (.leaf (4273330269983688:ℤ))))), (.branch 153 (.branch 126 (.leaf (1975332457376733:ℤ)) (.branch 143 (.leaf (2276429122652935:ℤ)) (.leaf (2664051706682078:ℤ)))) (.branch 170 (.leaf (2947604990462181:ℤ)) (.branch 185 (.leaf (3564593620878054:ℤ)) (.leaf (4316450969002894:ℤ))))), (.branch 153 (.branch 126 (.leaf (1987024539321077:ℤ)) (.branch 143 (.leaf (2295572582335987:ℤ)) (.leaf (2694905932715619:ℤ)))) (.branch 170 (.leaf (2988381085761880:ℤ)) (.branch 185 (.leaf (3630449900779011:ℤ)) (.leaf (4418499703451574:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 26 23) 8000 (endpointMeanRuns 26 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 26 23, EndpointRunConditions (endpointMeanCutoff 26 23) (endpointMeanBox 26 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 26 23 h) (endpointMeanCornerA 26 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 26 23, endpointJoint24Q (endpointMeanCornerK 26 23 h) (endpointMeanCornerA 26 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 26 23, endpointRunWeightQ (endpointMeanCutoff 26 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 26 23) = (5171791/12500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 26 23 h = (logRoundedQ ((endpointMeanCutoff 26 23:ℚ)/200)).2+(5171791/12500000000000:ℚ)+((endpointMeanRuns 26 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 26 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 26 23) r*endpointJoint24Q (endpointMeanCornerK 26 23 h) (endpointMeanCornerA 26 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 26 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 26 23 h≤endpointMeanCorner 26 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 26 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint26_23

namespace EndpointAnalyticJoint27_08
private noncomputable def weights : IntegerLookupTree := (.branch 1334 (.branch 944 (.leaf (99712880700000:ℤ)) (.leaf (40941984700000:ℤ))) (.branch 1842 (.leaf (21102867800000:ℤ)) (.leaf (29249265700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 158 (.branch 142 (.leaf (1809171241289925:ℤ)) (.leaf (2229396316435959:ℤ))) (.branch 182 (.leaf (2487894621325871:ℤ)) (.leaf (2976018704745196:ℤ)))), (.branch 158 (.branch 142 (.leaf (1818686191363291:ℤ)) (.leaf (2251919065882405:ℤ))) (.branch 182 (.leaf (2521222629624320:ℤ)) (.leaf (3035497074105147:ℤ)))), (.branch 158 (.branch 142 (.leaf (1812451280238610:ℤ)) (.leaf (2239022544125684:ℤ))) (.branch 182 (.leaf (2503915619058227:ℤ)) (.leaf (3010964526997279:ℤ)))), (.branch 158 (.branch 142 (.leaf (1822345163609150:ℤ)) (.leaf (2262710598667793:ℤ))) (.branch 182 (.leaf (2539243700365885:ℤ)) (.leaf (3075072599326952:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 27 8) 8000 (endpointMeanRuns 27 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 27 8, EndpointRunConditions (endpointMeanCutoff 27 8) (endpointMeanBox 27 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 27 8 h) (endpointMeanCornerA 27 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 8, endpointJoint24Q (endpointMeanCornerK 27 8 h) (endpointMeanCornerA 27 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 27 8, endpointRunWeightQ (endpointMeanCutoff 27 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 27 8) = (108139861/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 27 8 h = (logRoundedQ ((endpointMeanCutoff 27 8:ℚ)/200)).2+(108139861/250000000000000:ℚ)+((endpointMeanRuns 27 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 27 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 27 8) r*endpointJoint24Q (endpointMeanCornerK 27 8 h) (endpointMeanCornerA 27 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 27 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 27 8 h≤endpointMeanCorner 27 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 27 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint27_08

namespace EndpointAnalyticJoint27_09
private noncomputable def weights : IntegerLookupTree := (.branch 1334 (.branch 944 (.leaf (95654247900000:ℤ)) (.leaf (40630181400000:ℤ))) (.branch 1842 (.leaf (20968177500000:ℤ)) (.leaf (29091218800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 158 (.branch 142 (.leaf (1818686191363291:ℤ)) (.leaf (2251919065882405:ℤ))) (.branch 182 (.leaf (2521222629624320:ℤ)) (.leaf (3035497074105147:ℤ)))), (.branch 158 (.branch 142 (.leaf (1829451076991047:ℤ)) (.leaf (2277531013995287:ℤ))) (.branch 182 (.leaf (2559253219584186:ℤ)) (.leaf (3103837042921539:ℤ)))), (.branch 158 (.branch 142 (.leaf (1822345163609150:ℤ)) (.leaf (2262710598667793:ℤ))) (.branch 182 (.leaf (2539243700365885:ℤ)) (.leaf (3075072599326952:ℤ)))), (.branch 158 (.branch 142 (.leaf (1833541122557807:ℤ)) (.leaf (2289661203622376:ℤ))) (.branch 182 (.leaf (2579586722524154:ℤ)) (.leaf (3148832276865592:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 27 9) 8000 (endpointMeanRuns 27 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 27 9, EndpointRunConditions (endpointMeanCutoff 27 9) (endpointMeanBox 27 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 27 9 h) (endpointMeanCornerA 27 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 9, endpointJoint24Q (endpointMeanCornerK 27 9 h) (endpointMeanCornerA 27 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 27 9, endpointRunWeightQ (endpointMeanCutoff 27 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 27 9) = (431063013/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 27 9 h = (logRoundedQ ((endpointMeanCutoff 27 9:ℚ)/200)).2+(431063013/1000000000000000:ℚ)+((endpointMeanRuns 27 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 27 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 27 9) r*endpointJoint24Q (endpointMeanCornerK 27 9 h) (endpointMeanCornerA 27 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 27 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 27 9 h≤endpointMeanCorner 27 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 27 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint27_09

namespace EndpointAnalyticJoint27_10
private noncomputable def weights : IntegerLookupTree := (.branch 1334 (.branch 944 (.leaf (91741896300000:ℤ)) (.leaf (40322379400000:ℤ))) (.branch 1842 (.leaf (20835215600000:ℤ)) (.leaf (28935200100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 158 (.branch 142 (.leaf (1829451076991047:ℤ)) (.leaf (2277531013995287:ℤ))) (.branch 182 (.leaf (2559253219584186:ℤ)) (.leaf (3103837042921539:ℤ)))), (.branch 158 (.branch 142 (.leaf (1840279680462561:ℤ)) (.leaf (2303434256718207:ℤ))) (.branch 182 (.leaf (2597857470019610:ℤ)) (.leaf (3173715590502406:ℤ)))), (.branch 158 (.branch 142 (.leaf (1833541122557807:ℤ)) (.leaf (2289661203622376:ℤ))) (.branch 182 (.leaf (2579586722524154:ℤ)) (.leaf (3148832276865592:ℤ)))), (.branch 158 (.branch 142 (.leaf (1844805866223695:ℤ)) (.leaf (2316932810789009:ℤ))) (.branch 182 (.leaf (2620570706964473:ℤ)) (.leaf (3224361177684290:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 27 10) 8000 (endpointMeanRuns 27 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 27 10, EndpointRunConditions (endpointMeanCutoff 27 10) (endpointMeanBox 27 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 27 10 h) (endpointMeanCornerA 27 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 10, endpointJoint24Q (endpointMeanCornerK 27 10 h) (endpointMeanCornerA 27 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 27 10, endpointRunWeightQ (endpointMeanCutoff 27 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 27 10) = (214792893/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 27 10 h = (logRoundedQ ((endpointMeanCutoff 27 10:ℚ)/200)).2+(214792893/500000000000000:ℚ)+((endpointMeanRuns 27 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 27 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 27 10) r*endpointJoint24Q (endpointMeanCornerK 27 10 h) (endpointMeanCornerA 27 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 27 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 27 10 h≤endpointMeanCorner 27 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 27 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint27_10

namespace EndpointAnalyticJoint27_11
private noncomputable def weights : IntegerLookupTree := (.branch 1334 (.branch 944 (.leaf (87970358300000:ℤ)) (.leaf (40018477200000:ℤ))) (.branch 1842 (.leaf (20703938400000:ℤ)) (.branch 2975 (.leaf (10912349800000:ℤ)) (.leaf (1546278700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 126 (.leaf (1840279680462561:ℤ)) (.leaf (2058786824458232:ℤ))) (.branch 158 (.leaf (2303434256718207:ℤ)) (.branch 182 (.leaf (2597857470019610:ℤ)) (.leaf (3173715590502406:ℤ))))), (.branch 142 (.branch 126 (.leaf (1851172378926621:ℤ)) (.leaf (2076100037585677:ℤ))) (.branch 158 (.leaf (2329632107057639:ℤ)) (.branch 182 (.leaf (2637044034131650:ℤ)) (.leaf (3245167355795568:ℤ))))), (.branch 142 (.branch 126 (.leaf (1844805866223695:ℤ)) (.leaf (2066792519438529:ℤ))) (.branch 158 (.leaf (2316932810789009:ℤ)) (.branch 182 (.leaf (2620570706964473:ℤ)) (.leaf (3224361177684290:ℤ))))), (.branch 142 (.branch 126 (.leaf (1856139817200123:ℤ)) (.leaf (2084908521422093:ℤ))) (.branch 158 (.leaf (2344529243548307:ℤ)) (.branch 182 (.leaf (2662205837173970:ℤ)) (.leaf (3301701738940034:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 27 11) 8000 (endpointMeanRuns 27 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 27 11, EndpointRunConditions (endpointMeanCutoff 27 11) (endpointMeanBox 27 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 27 11 h) (endpointMeanCornerA 27 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 11, endpointJoint24Q (endpointMeanCornerK 27 11 h) (endpointMeanCornerA 27 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 27 11, endpointRunWeightQ (endpointMeanCutoff 27 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 27 11) = (107031819/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 27 11 h = (logRoundedQ ((endpointMeanCutoff 27 11:ℚ)/200)).2+(107031819/250000000000000:ℚ)+((endpointMeanRuns 27 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 27 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 27 11) r*endpointJoint24Q (endpointMeanCornerK 27 11 h) (endpointMeanCornerA 27 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 27 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 27 11 h≤endpointMeanCorner 27 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 27 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint27_11

namespace EndpointAnalyticJoint27_12
private noncomputable def weights : IntegerLookupTree := (.branch 1334 (.branch 944 (.leaf (84334390900000:ℤ)) (.leaf (39718377200000:ℤ))) (.branch 1842 (.leaf (20574303600000:ℤ)) (.branch 2975 (.leaf (10853869800000:ℤ)) (.leaf (1539339400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 126 (.leaf (1851172378926621:ℤ)) (.leaf (2076100037585677:ℤ))) (.branch 158 (.leaf (2329632107057639:ℤ)) (.branch 182 (.leaf (2637044034131650:ℤ)) (.leaf (3245167355795568:ℤ))))), (.branch 142 (.branch 126 (.leaf (1862129551764378:ℤ)) (.leaf (2093558844878211:ℤ))) (.branch 158 (.leaf (2356127915700159:ℤ)) (.branch 182 (.leaf (2676821695647849:ℤ)) (.leaf (3318227757596296:ℤ))))), (.branch 142 (.branch 126 (.leaf (1856139817200123:ℤ)) (.leaf (2084908521422093:ℤ))) (.branch 158 (.leaf (2344529243548307:ℤ)) (.branch 182 (.leaf (2662205837173970:ℤ)) (.leaf (3301701738940034:ℤ))))), (.branch 142 (.branch 126 (.leaf (1867543400676690:ℤ)) (.leaf (2103183315120248:ℤ))) (.branch 158 (.leaf (2372454370820236:ℤ)) (.branch 182 (.leaf (2704502458433090:ℤ)) (.leaf (3380897415701062:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 27 12) 8000 (endpointMeanRuns 27 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 27 12, EndpointRunConditions (endpointMeanCutoff 27 12) (endpointMeanBox 27 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 27 12 h) (endpointMeanCornerA 27 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 12, endpointJoint24Q (endpointMeanCornerK 27 12 h) (endpointMeanCornerA 27 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 27 12, endpointRunWeightQ (endpointMeanCutoff 27 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 27 12) = (213343507/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 27 12 h = (logRoundedQ ((endpointMeanCutoff 27 12:ℚ)/200)).2+(213343507/500000000000000:ℚ)+((endpointMeanRuns 27 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 27 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 27 12) r*endpointJoint24Q (endpointMeanCornerK 27 12 h) (endpointMeanCornerA 27 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 27 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 27 12 h≤endpointMeanCorner 27 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 27 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint27_12

namespace EndpointAnalyticJoint27_13
private noncomputable def weights : IntegerLookupTree := (.branch 1407 (.branch 774 (.leaf (41855449100000:ℤ)) (.branch 1090 (.leaf (46082726300000:ℤ)) (.leaf (23543268800000:ℤ)))) (.branch 1842 (.leaf (15135458800000:ℤ)) (.branch 2975 (.leaf (10796112400000:ℤ)) (.leaf (1532485800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 126 (.leaf (1862129551764378:ℤ)) (.branch 142 (.leaf (2093558844878211:ℤ)) (.leaf (2356127915700159:ℤ)))) (.branch 171 (.leaf (2611387691233915:ℤ)) (.branch 200 (.leaf (2994988530922399:ℤ)) (.leaf (3999464427229591:ℤ))))), (.branch 155 (.branch 126 (.leaf (1873151580602559:ℤ)) (.branch 142 (.leaf (2111164470699023:ℤ)) (.leaf (2382925071441000:ℤ)))) (.branch 171 (.leaf (2648791336570065:ℤ)) (.branch 200 (.leaf (3051249571581222:ℤ)) (.leaf (4120049219012106:ℤ))))), (.branch 155 (.branch 126 (.leaf (1867543400676690:ℤ)) (.branch 142 (.leaf (2103183315120248:ℤ)) (.leaf (2372454370820236:ℤ)))) (.branch 171 (.leaf (2636447325691125:ℤ)) (.branch 200 (.leaf (3037825095068154:ℤ)) (.leaf (4120622606382048:ℤ))))), (.branch 155 (.branch 126 (.leaf (1879017044455238:ℤ)) (.branch 142 (.leaf (2121618292385828:ℤ)) (.leaf (2400712107606545:ℤ)))) (.branch 171 (.leaf (2676175255601382:ℤ)) (.branch 200 (.leaf (3098273583539614:ℤ)) (.leaf (4254616371322464:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 27 13) 8000 (endpointMeanRuns 27 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 27 13, EndpointRunConditions (endpointMeanCutoff 27 13) (endpointMeanBox 27 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 27 13 h) (endpointMeanCornerA 27 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 13, endpointJoint24Q (endpointMeanCornerK 27 13 h) (endpointMeanCornerA 27 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 27 13, endpointRunWeightQ (endpointMeanCutoff 27 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 27 13) = (106316137/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 27 13 h = (logRoundedQ ((endpointMeanCutoff 27 13:ℚ)/200)).2+(106316137/250000000000000:ℚ)+((endpointMeanRuns 27 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 27 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 27 13) r*endpointJoint24Q (endpointMeanCornerK 27 13 h) (endpointMeanCornerA 27 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 27 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 27 13 h≤endpointMeanCorner 27 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 27 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint27_13

namespace EndpointAnalyticJoint27_14
private noncomputable def weights : IntegerLookupTree := (.branch 1090 (.branch 774 (.leaf (39427375100000:ℤ)) (.branch 944 (.leaf (24289795900000:ℤ)) (.leaf (15013379400000:ℤ)))) (.branch 1842 (.branch 1407 (.leaf (23379526100000:ℤ)) (.leaf (15043555300000:ℤ))) (.branch 2975 (.leaf (10739059900000:ℤ)) (.leaf (1525715800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 126 (.leaf (1873151580602559:ℤ)) (.branch 142 (.leaf (2111164470699023:ℤ)) (.leaf (2382925071441000:ℤ)))) (.branch 182 (.branch 171 (.leaf (2648791336570065:ℤ)) (.leaf (3051249571581222:ℤ))) (.branch 200 (.leaf (3392933012104461:ℤ)) (.leaf (4120049219012106:ℤ))))), (.branch 155 (.branch 126 (.leaf (1884238849326763:ℤ)) (.branch 142 (.leaf (2128918149707495:ℤ)) (.leaf (2410027001617479:ℤ)))) (.branch 182 (.branch 171 (.leaf (2686730724909493:ℤ)) (.leaf (3108567479290898:ℤ))) (.branch 200 (.leaf (3469320150877011:ℤ)) (.leaf (4244269670587030:ℤ))))), (.branch 155 (.branch 126 (.leaf (1879017044455238:ℤ)) (.branch 142 (.leaf (2121618292385828:ℤ)) (.leaf (2400712107606545:ℤ)))) (.branch 182 (.branch 171 (.leaf (2676175255601382:ℤ)) (.leaf (3098273583539614:ℤ))) (.branch 200 (.leaf (3461992705362811:ℤ)) (.leaf (4254616371322464:ℤ))))), (.branch 155 (.branch 126 (.leaf (1890561178965890:ℤ)) (.branch 142 (.leaf (2140214857271629:ℤ)) (.leaf (2429306415539639:ℤ)))) (.branch 182 (.branch 171 (.leaf (2716501835217086:ℤ)) (.leaf (3159924912742232:ℤ))) (.branch 200 (.leaf (3545033172649528:ℤ)) (.leaf (4392967324668132:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 27 14) 8000 (endpointMeanRuns 27 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 27 14, EndpointRunConditions (endpointMeanCutoff 27 14) (endpointMeanBox 27 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 27 14 h) (endpointMeanCornerA 27 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 14, endpointJoint24Q (endpointMeanCornerK 27 14 h) (endpointMeanCornerA 27 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 27 14, endpointRunWeightQ (endpointMeanCutoff 27 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 27 14) = (211929723/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 27 14 h = (logRoundedQ ((endpointMeanCutoff 27 14:ℚ)/200)).2+(211929723/500000000000000:ℚ)+((endpointMeanRuns 27 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 27 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 27 14) r*endpointJoint24Q (endpointMeanCornerK 27 14 h) (endpointMeanCornerA 27 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 27 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 27 14 h≤endpointMeanCorner 27 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 27 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint27_14

namespace EndpointAnalyticJoint27_15
private noncomputable def weights : IntegerLookupTree := (.branch 1090 (.branch 774 (.leaf (36771397500000:ℤ)) (.branch 944 (.leaf (24047876500000:ℤ)) (.leaf (14880653500000:ℤ)))) (.branch 1842 (.branch 1407 (.leaf (23194806700000:ℤ)) (.leaf (14939878300000:ℤ))) (.branch 2975 (.leaf (10674698700000:ℤ)) (.leaf (1518078600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 126 (.leaf (1884238849326763:ℤ)) (.branch 142 (.leaf (2128918149707495:ℤ)) (.leaf (2410027001617479:ℤ)))) (.branch 182 (.branch 171 (.leaf (2686730724909493:ℤ)) (.leaf (3108567479290898:ℤ))) (.branch 200 (.leaf (3469320150877011:ℤ)) (.leaf (4244269670587030:ℤ))))), (.branch 155 (.branch 126 (.leaf (1895391744094814:ℤ)) (.branch 142 (.leaf (2146821126945788:ℤ)) (.leaf (2437437172547348:ℤ)))) (.branch 182 (.branch 171 (.leaf (2725213529850938:ℤ)) (.leaf (3166962107362882:ℤ))) (.branch 200 (.leaf (3547427039184560:ℤ)) (.leaf (4372235397950956:ℤ))))), (.branch 155 (.branch 126 (.leaf (1890561178965890:ℤ)) (.branch 142 (.leaf (2140214857271629:ℤ)) (.leaf (2429306415539639:ℤ)))) (.branch 182 (.branch 171 (.leaf (2716501835217086:ℤ)) (.leaf (3159924912742232:ℤ))) (.branch 200 (.leaf (3545033172649528:ℤ)) (.leaf (4392967324668132:ℤ))))), (.branch 155 (.branch 126 (.leaf (1902176237283218:ℤ)) (.branch 142 (.leaf (2158974426137363:ℤ)) (.leaf (2458241303437975:ℤ)))) (.branch 182 (.branch 171 (.leaf (2757436085432875:ℤ)) (.leaf (3222803017531312:ℤ))) (.branch 200 (.leaf (3630065475215539:ℤ)) (.leaf (4535817152793822:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 27 15) 8000 (endpointMeanRuns 27 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 27 15, EndpointRunConditions (endpointMeanCutoff 27 15) (endpointMeanBox 27 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 27 15 h) (endpointMeanCornerA 27 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 15, endpointJoint24Q (endpointMeanCornerK 27 15 h) (endpointMeanCornerA 27 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 27 15, endpointRunWeightQ (endpointMeanCutoff 27 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 27 15) = (422274339/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 27 15 h = (logRoundedQ ((endpointMeanCutoff 27 15:ℚ)/200)).2+(422274339/1000000000000000:ℚ)+((endpointMeanRuns 27 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 27 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 27 15) r*endpointJoint24Q (endpointMeanCornerK 27 15 h) (endpointMeanCornerA 27 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 27 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 27 15 h≤endpointMeanCorner 27 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 27 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint27_15

namespace EndpointAnalyticJoint27_16
private noncomputable def weights : IntegerLookupTree := (.branch 1209 (.branch 944 (.branch 774 (.leaf (34547205300000:ℤ)) (.leaf (23838895600000:ℤ))) (.branch 1090 (.leaf (14765998900000:ℤ)) (.leaf (8982647800000:ℤ)))) (.branch 1842 (.branch 1407 (.leaf (11414753000000:ℤ)) (.leaf (14850317400000:ℤ))) (.branch 2975 (.leaf (10619100500000:ℤ)) (.leaf (1511481200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 142 (.branch 126 (.leaf (1895391744094814:ℤ)) (.leaf (2146821126945788:ℤ))) (.branch 155 (.leaf (2437437172547348:ℤ)) (.leaf (2725213529850938:ℤ)))) (.branch 182 (.branch 171 (.leaf (2959736225812371:ℤ)) (.leaf (3166962107362882:ℤ))) (.branch 200 (.leaf (3547427039184560:ℤ)) (.leaf (4372235397950956:ℤ))))), (.branch 164 (.branch 142 (.branch 126 (.leaf (1906610653350227:ℤ)) (.leaf (2164874657926152:ℤ))) (.branch 155 (.leaf (2465159089972135:ℤ)) (.leaf (2764247534904264:ℤ)))) (.branch 182 (.branch 171 (.leaf (3009183895486337:ℤ)) (.leaf (3226453682054298:ℤ))) (.branch 200 (.leaf (3627292394781314:ℤ)) (.leaf (4504059322048532:ℤ))))), (.branch 164 (.branch 142 (.branch 126 (.leaf (1902176237283218:ℤ)) (.leaf (2158974426137363:ℤ))) (.branch 155 (.leaf (2458241303437975:ℤ)) (.leaf (2757436085432875:ℤ)))) (.branch 182 (.branch 171 (.leaf (3003538010990697:ℤ)) (.leaf (3222803017531312:ℤ))) (.branch 200 (.leaf (3630065475215539:ℤ)) (.leaf (4535817152793822:ℤ))))), (.branch 164 (.branch 142 (.branch 126 (.leaf (1913862655142477:ℤ)) (.leaf (2177898427757510:ℤ))) (.branch 155 (.leaf (2487520827868099:ℤ)) (.leaf (2798987163076870:ℤ)))) (.branch 182 (.branch 171 (.leaf (3056522598259279:ℤ)) (.leaf (3286932309032429:ℤ))) (.branch 200 (.leaf (3717137389860625:ℤ)) (.leaf (4683312149409836:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 27 16) 8000 (endpointMeanRuns 27 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 27 16, EndpointRunConditions (endpointMeanCutoff 27 16) (endpointMeanBox 27 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 27 16 h) (endpointMeanCornerA 27 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 16, endpointJoint24Q (endpointMeanCornerK 27 16 h) (endpointMeanCornerA 27 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 27 16, endpointRunWeightQ (endpointMeanCutoff 27 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 27 16) = (420905051/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 27 16 h = (logRoundedQ ((endpointMeanCutoff 27 16:ℚ)/200)).2+(420905051/1000000000000000:ℚ)+((endpointMeanRuns 27 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 27 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 27 16) r*endpointJoint24Q (endpointMeanCornerK 27 16 h) (endpointMeanCornerA 27 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 27 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 27 16 h≤endpointMeanCorner 27 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 27 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint27_16

namespace EndpointAnalyticJoint27_17
private noncomputable def weights : IntegerLookupTree := (.branch 1209 (.branch 944 (.branch 774 (.leaf (32412304500000:ℤ)) (.leaf (23632371300000:ℤ))) (.branch 1090 (.leaf (14652692100000:ℤ)) (.leaf (8918966800000:ℤ)))) (.branch 1842 (.branch 1407 (.leaf (11339431600000:ℤ)) (.leaf (14761809300000:ℤ))) (.branch 2275 (.leaf (5288500700000:ℤ)) (.branch 2975 (.leaf (2656495500000:ℤ)) (.leaf (1504961300000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 134 (.branch 126 (.leaf (1906610653350227:ℤ)) (.leaf (2164874657926152:ℤ))) (.branch 142 (.leaf (2306946358366619:ℤ)) (.leaf (2465159089972135:ℤ)))) (.branch 171 (.branch 164 (.leaf (2764247534904264:ℤ)) (.leaf (3009183895486337:ℤ))) (.branch 182 (.leaf (3226453682054298:ℤ)) (.branch 200 (.leaf (3627292394781314:ℤ)) (.leaf (4504059322048532:ℤ)))))), (.branch 155 (.branch 134 (.branch 126 (.leaf (1917895967835733:ℤ)) (.leaf (2183080008718964:ℤ))) (.branch 142 (.leaf (2329573038042559:ℤ)) (.leaf (2493196299505513:ℤ)))) (.branch 171 (.branch 164 (.leaf (2803840635064745:ℤ)) (.leaf (3059457676627554:ℤ))) (.branch 182 (.leaf (3287062809573718:ℤ)) (.branch 200 (.leaf (3708955807097522:ℤ)) (.leaf (4639857768417397:ℤ)))))), (.branch 155 (.branch 134 (.branch 126 (.leaf (1913862655142477:ℤ)) (.leaf (2177898427757510:ℤ))) (.branch 142 (.leaf (2324019459651860:ℤ)) (.leaf (2487520827868099:ℤ)))) (.branch 171 (.branch 164 (.leaf (2798987163076870:ℤ)) (.leaf (3056522598259279:ℤ))) (.branch 182 (.leaf (3286932309032429:ℤ)) (.branch 200 (.leaf (3717137389860625:ℤ)) (.leaf (4683312149409836:ℤ)))))), (.branch 155 (.branch 134 (.branch 126 (.leaf (1925620870955940:ℤ)) (.leaf (2196988303430171:ℤ))) (.branch 142 (.leaf (2347831708015350:ℤ)) (.leaf (2517149093713335:ℤ)))) (.branch 171 (.branch 164 (.leaf (2841164362959019:ℤ)) (.leaf (3110441872046812:ℤ))) (.branch 182 (.leaf (3352337684118568:ℤ)) (.branch 200 (.leaf (3806297839374229:ℤ)) (.leaf (4835603365382559:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 27 17) 8000 (endpointMeanRuns 27 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 27 17, EndpointRunConditions (endpointMeanCutoff 27 17) (endpointMeanBox 27 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 27 17 h) (endpointMeanCornerA 27 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 17, endpointJoint24Q (endpointMeanCornerK 27 17 h) (endpointMeanCornerA 27 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 27 17, endpointRunWeightQ (endpointMeanCutoff 27 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 27 17) = (419551859/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 27 17 h = (logRoundedQ ((endpointMeanCutoff 27 17:ℚ)/200)).2+(419551859/1000000000000000:ℚ)+((endpointMeanRuns 27 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 27 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 27 17) r*endpointJoint24Q (endpointMeanCornerK 27 17 h) (endpointMeanCornerA 27 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 27 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 27 17 h≤endpointMeanCorner 27 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 27 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint27_17

namespace EndpointAnalyticJoint27_18
private noncomputable def weights : IntegerLookupTree := (.branch 1209 (.branch 944 (.branch 774 (.leaf (30363184100000:ℤ)) (.leaf (23428246600000:ℤ))) (.branch 1090 (.leaf (14540701700000:ℤ)) (.leaf (8856025700000:ℤ)))) (.branch 1842 (.branch 1407 (.leaf (11264985300000:ℤ)) (.leaf (14674329500000:ℤ))) (.branch 2275 (.leaf (5260664900000:ℤ)) (.branch 2975 (.leaf (2643784600000:ℤ)) (.leaf (1498517200000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 134 (.branch 126 (.leaf (1917895967835733:ℤ)) (.leaf (2183080008718964:ℤ))) (.branch 142 (.leaf (2329573038042559:ℤ)) (.leaf (2493196299505513:ℤ)))) (.branch 171 (.branch 164 (.leaf (2803840635064745:ℤ)) (.leaf (3059457676627554:ℤ))) (.branch 182 (.leaf (3287062809573718:ℤ)) (.branch 200 (.leaf (3708955807097522:ℤ)) (.leaf (4639857768417397:ℤ)))))), (.branch 155 (.branch 134 (.branch 126 (.leaf (1929248080606886:ℤ)) (.leaf (2201438456041536:ℤ))) (.branch 142 (.leaf (2352421641661947:ℤ)) (.leaf (2521552387086814:ℤ)))) (.branch 171 (.branch 164 (.leaf (2844000838409925:ℤ)) (.leaf (3110571370900712:ℤ))) (.branch 182 (.leaf (3348810483218585:ℤ)) (.branch 200 (.leaf (3792457756864069:ℤ)) (.leaf (4779750569837477:ℤ)))))), (.branch 155 (.branch 134 (.branch 126 (.leaf (1925620870955940:ℤ)) (.leaf (2196988303430171:ℤ))) (.branch 142 (.leaf (2347831708015350:ℤ)) (.leaf (2517149093713335:ℤ)))) (.branch 171 (.branch 164 (.leaf (2841164362959019:ℤ)) (.leaf (3110441872046812:ℤ))) (.branch 182 (.leaf (3352337684118568:ℤ)) (.branch 200 (.leaf (3806297839374229:ℤ)) (.leaf (4835603365382559:ℤ)))))), (.branch 155 (.branch 134 (.branch 126 (.leaf (1937451325829372:ℤ)) (.leaf (2216245507086790:ℤ))) (.branch 142 (.leaf (2371887940210287:ℤ)) (.leaf (2547130254749304:ℤ)))) (.branch 171 (.branch 164 (.leaf (2883977119950311:ℤ)) (.leaf (3165312320900884:ℤ))) (.branch 182 (.leaf (3419044535075812:ℤ)) (.branch 200 (.leaf (3897596920023487:ℤ)) (.leaf (4992846763426985:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 27 18) 8000 (endpointMeanRuns 27 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 27 18, EndpointRunConditions (endpointMeanCutoff 27 18) (endpointMeanBox 27 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 27 18 h) (endpointMeanCornerA 27 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 18, endpointJoint24Q (endpointMeanCornerK 27 18 h) (endpointMeanCornerA 27 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 27 18, endpointRunWeightQ (endpointMeanCutoff 27 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 27 18) = (41821439/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 27 18 h = (logRoundedQ ((endpointMeanCutoff 27 18:ℚ)/200)).2+(41821439/100000000000000:ℚ)+((endpointMeanRuns 27 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 27 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 27 18) r*endpointJoint24Q (endpointMeanCornerK 27 18 h) (endpointMeanCornerA 27 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 27 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 27 18 h≤endpointMeanCorner 27 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 27 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint27_18

namespace EndpointAnalyticJoint27_19
private noncomputable def weights : IntegerLookupTree := (.branch 1209 (.branch 944 (.branch 774 (.leaf (28396478800000:ℤ)) (.leaf (23226466200000:ℤ))) (.branch 1090 (.leaf (14429997500000:ℤ)) (.leaf (8793807500000:ℤ)))) (.branch 1842 (.branch 1407 (.leaf (11191394100000:ℤ)) (.leaf (14587854400000:ℤ))) (.branch 2275 (.leaf (5233148900000:ℤ)) (.branch 2975 (.leaf (2631219600000:ℤ)) (.leaf (1492147100000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 134 (.branch 126 (.leaf (1929248080606886:ℤ)) (.leaf (2201438456041536:ℤ))) (.branch 142 (.leaf (2352421641661947:ℤ)) (.leaf (2521552387086814:ℤ)))) (.branch 171 (.branch 164 (.leaf (2844000838409925:ℤ)) (.leaf (3110571370900712:ℤ))) (.branch 182 (.leaf (3348810483218585:ℤ)) (.branch 200 (.leaf (3792457756864069:ℤ)) (.leaf (4779750569837477:ℤ)))))), (.branch 155 (.branch 134 (.branch 126 (.leaf (1940667387045747:ℤ)) (.leaf (2219951287347630:ℤ))) (.branch 142 (.leaf (2375494345869222:ℤ)) (.leaf (2550230979439631:ℤ)))) (.branch 171 (.branch 164 (.leaf (2884736267719283:ℤ)) (.leaf (3162539010551901:ℤ))) (.branch 182 (.leaf (3411718090646730:ℤ)) (.branch 200 (.leaf (3877839636178840:ℤ)) (.leaf (4923861172075156:ℤ)))))), (.branch 155 (.branch 134 (.branch 126 (.leaf (1937451325829372:ℤ)) (.leaf (2216245507086790:ℤ))) (.branch 142 (.leaf (2371887940210287:ℤ)) (.leaf (2547130254749304:ℤ)))) (.branch 171 (.branch 164 (.leaf (2883977119950311:ℤ)) (.leaf (3165312320900884:ℤ))) (.branch 182 (.leaf (3419044535075812:ℤ)) (.branch 200 (.leaf (3897596920023487:ℤ)) (.leaf (4992846763426985:ℤ)))))), (.branch 155 (.branch 134 (.branch 126 (.leaf (1949354463578558:ℤ)) (.leaf (2235671505402944:ℤ))) (.branch 142 (.leaf (2396190656131228:ℤ)) (.leaf (2577468514226246:ℤ)))) (.branch 171 (.branch 164 (.leaf (2927435011093325:ℤ)) (.leaf (3221150724239011:ℤ))) (.branch 182 (.leaf (3487078759461367:ℤ)) (.branch 200 (.leaf (3991085929700673:ℤ)) (.leaf (5155203377829379:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 27 19) 8000 (endpointMeanRuns 27 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 27 19, EndpointRunConditions (endpointMeanCutoff 27 19) (endpointMeanBox 27 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 27 19 h) (endpointMeanCornerA 27 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 19, endpointJoint24Q (endpointMeanCornerK 27 19 h) (endpointMeanCornerA 27 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 27 19, endpointRunWeightQ (endpointMeanCutoff 27 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 27 19) = (416892281/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 27 19 h = (logRoundedQ ((endpointMeanCutoff 27 19:ℚ)/200)).2+(416892281/1000000000000000:ℚ)+((endpointMeanRuns 27 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 27 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 27 19) r*endpointJoint24Q (endpointMeanCornerK 27 19 h) (endpointMeanCornerA 27 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 27 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 27 19 h≤endpointMeanCorner 27 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 27 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint27_19

namespace EndpointAnalyticJoint27_20
private noncomputable def weights : IntegerLookupTree := (.branch 1209 (.branch 944 (.branch 774 (.leaf (26245599700000:ℤ)) (.leaf (22998662500000:ℤ))) (.branch 1090 (.leaf (14305016000000:ℤ)) (.leaf (8723565100000:ℤ)))) (.branch 1842 (.branch 1407 (.leaf (11108311800000:ℤ)) (.leaf (14490226800000:ℤ))) (.branch 2975 (.leaf (10395561100000:ℤ)) (.leaf (1484955500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 164 (.branch 142 (.branch 126 (.leaf (1940667387045747:ℤ)) (.leaf (2219951287347630:ℤ))) (.branch 155 (.leaf (2550230979439631:ℤ)) (.leaf (2884736267719283:ℤ)))) (.branch 182 (.branch 171 (.leaf (3162539010551901:ℤ)) (.leaf (3411718090646730:ℤ))) (.branch 200 (.leaf (3877839636178840:ℤ)) (.leaf (4923861172075156:ℤ))))), (.branch 164 (.branch 142 (.branch 126 (.leaf (1952154284874673:ℤ)) (.leaf (2238619800917757:ℤ))) (.branch 155 (.leaf (2579235744535698:ℤ)) (.leaf (2926055162117195:ℤ)))) (.branch 182 (.branch 171 (.leaf (3215374862260909:ℤ)) (.leaf (3475807421284403:ℤ))) (.branch 200 (.leaf (3965143769024884:ℤ)) (.leaf (5072316742815655:ℤ))))), (.branch 164 (.branch 142 (.branch 126 (.leaf (1949354463578558:ℤ)) (.leaf (2235671505402944:ℤ))) (.branch 155 (.leaf (2577468514226246:ℤ)) (.leaf (2927435011093325:ℤ)))) (.branch 182 (.branch 171 (.leaf (3221150724239011:ℤ)) (.leaf (3487078759461367:ℤ))) (.branch 200 (.leaf (3991085929700673:ℤ)) (.leaf (5155203377829379:ℤ))))), (.branch 164 (.branch 142 (.branch 126 (.leaf (1961330730745962:ℤ)) (.leaf (2255267777910008:ℤ))) (.branch 155 (.leaf (2608168125458312:ℤ)) (.leaf (2971547757744566:ℤ)))) (.branch 182 (.branch 171 (.leaf (3277974157479799:ℤ)) (.leaf (3556466770157769:ℤ))) (.branch 200 (.leaf (4086817396745761:ℤ)) (.leaf (5322839479363911:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 27 20) 8000 (endpointMeanRuns 27 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 27 20, EndpointRunConditions (endpointMeanCutoff 27 20) (endpointMeanBox 27 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 27 20 h) (endpointMeanCornerA 27 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 20, endpointJoint24Q (endpointMeanCornerK 27 20 h) (endpointMeanCornerA 27 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 27 20, endpointRunWeightQ (endpointMeanCutoff 27 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 27 20) = (415399663/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 27 20 h = (logRoundedQ ((endpointMeanCutoff 27 20:ℚ)/200)).2+(415399663/1000000000000000:ℚ)+((endpointMeanRuns 27 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 27 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 27 20) r*endpointJoint24Q (endpointMeanCornerK 27 20 h) (endpointMeanCornerA 27 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 27 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 27 20 h≤endpointMeanCorner 27 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 27 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint27_20

namespace EndpointAnalyticJoint27_21
private noncomputable def weights : IntegerLookupTree := (.branch 1407 (.branch 944 (.branch 774 (.leaf (24444804600000:ℤ)) (.leaf (22801728800000:ℤ))) (.branch 1090 (.leaf (14196970900000:ℤ)) (.leaf (22243300800000:ℤ)))) (.branch 2275 (.branch 1842 (.leaf (14405828800000:ℤ)) (.leaf (5175228900000:ℤ))) (.branch 2975 (.leaf (2604771000000:ℤ)) (.leaf (1478738400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 134 (.branch 126 (.leaf (1952154284874673:ℤ)) (.leaf (2238619800917757:ℤ))) (.branch 142 (.leaf (2398793348657502:ℤ)) (.leaf (2579235744535698:ℤ)))) (.branch 182 (.branch 171 (.leaf (2926055162117195:ℤ)) (.leaf (3475807421284403:ℤ))) (.branch 200 (.leaf (3965143769024884:ℤ)) (.leaf (5072316742815655:ℤ))))), (.branch 155 (.branch 134 (.branch 126 (.leaf (1963709174170150:ℤ)) (.leaf (2257445305950222:ℤ))) (.branch 142 (.leaf (2422320869577965:ℤ)) (.leaf (2608570392064004:ℤ)))) (.branch 182 (.branch 171 (.leaf (2967965878739327:ℤ)) (.leaf (3541100673873553:ℤ))) (.branch 200 (.leaf (4054413432250490:ℤ)) (.leaf (5225248283879785:ℤ))))), (.branch 155 (.branch 134 (.branch 126 (.leaf (1961330730745962:ℤ)) (.leaf (2255267777910008:ℤ))) (.branch 142 (.leaf (2420742381287015:ℤ)) (.leaf (2608168125458312:ℤ)))) (.branch 182 (.branch 171 (.leaf (2971547757744566:ℤ)) (.leaf (3556466770157769:ℤ))) (.branch 200 (.leaf (4086817396745761:ℤ)) (.leaf (5322839479363911:ℤ))))), (.branch 155 (.branch 134 (.branch 126 (.leaf (1973380576617463:ℤ)) (.leaf (2275035817107860:ℤ))) (.branch 142 (.leaf (2445545667063238:ℤ)) (.leaf (2639233392419869:ℤ)))) (.branch 182 (.branch 171 (.leaf (3016325227749096:ℤ)) (.leaf (3627235505627117:ℤ))) (.branch 200 (.leaf (4184845109460331:ℤ)) (.leaf (5495926745571887:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 27 21) 8000 (endpointMeanRuns 27 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 27 21, EndpointRunConditions (endpointMeanCutoff 27 21) (endpointMeanBox 27 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 27 21 h) (endpointMeanCornerA 27 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 21, endpointJoint24Q (endpointMeanCornerK 27 21 h) (endpointMeanCornerA 27 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 27 21, endpointRunWeightQ (endpointMeanCutoff 27 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 27 21) = (414109311/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 27 21 h = (logRoundedQ ((endpointMeanCutoff 27 21:ℚ)/200)).2+(414109311/1000000000000000:ℚ)+((endpointMeanRuns 27 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 27 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 27 21) r*endpointJoint24Q (endpointMeanCornerK 27 21 h) (endpointMeanCornerA 27 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 27 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 27 21 h≤endpointMeanCorner 27 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 27 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint27_21

namespace EndpointAnalyticJoint27_22
private noncomputable def weights : IntegerLookupTree := (.branch 1209 (.branch 860 (.leaf (38243209500000:ℤ)) (.branch 992 (.leaf (14939553200000:ℤ)) (.leaf (18940621900000:ℤ)))) (.branch 1842 (.branch 1407 (.leaf (10965460800000:ℤ)) (.leaf (14322366400000:ℤ))) (.branch 2975 (.leaf (10291355700000:ℤ)) (.leaf (1472590300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 126 (.leaf (1963709174170150:ℤ)) (.branch 142 (.leaf (2257445305950222:ℤ)) (.leaf (2608570392064004:ℤ)))) (.branch 178 (.branch 164 (.leaf (2967965878739327:ℤ)) (.leaf (3269093431057832:ℤ))) (.branch 190 (.leaf (3853898148763445:ℤ)) (.leaf (4513208854438763:ℤ))))), (.branch 155 (.branch 126 (.leaf (1975332457376733:ℤ)) (.branch 142 (.leaf (2276429122652935:ℤ)) (.leaf (2638238673905277:ℤ)))) (.branch 178 (.branch 164 (.leaf (3010476894422988:ℤ)) (.leaf (3323709464305158:ℤ))) (.branch 190 (.leaf (3935164355905043:ℤ)) (.leaf (4628935655878960:ℤ))))), (.branch 155 (.branch 126 (.leaf (1973380576617463:ℤ)) (.branch 142 (.leaf (2275035817107860:ℤ)) (.leaf (2639233392419869:ℤ)))) (.branch 178 (.branch 164 (.leaf (3016325227749096:ℤ)) (.leaf (3335799997264615:ℤ))) (.branch 190 (.leaf (3965819141695023:ℤ)) (.leaf (4691957944506306:ℤ))))), (.branch 155 (.branch 126 (.leaf (1985504453239234:ℤ)) (.branch 142 (.leaf (2294977128578545:ℤ)) (.leaf (2670668670348883:ℤ)))) (.branch 178 (.branch 164 (.leaf (3061777437647939:ℤ)) (.leaf (3394645926771366:ℤ))) (.branch 190 (.leaf (4054718130409874:ℤ)) (.leaf (4820771883035019:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 27 22) 8000 (endpointMeanRuns 27 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 27 22, EndpointRunConditions (endpointMeanCutoff 27 22) (endpointMeanBox 27 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 27 22 h) (endpointMeanCornerA 27 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 22, endpointJoint24Q (endpointMeanCornerK 27 22 h) (endpointMeanCornerA 27 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 27 22, endpointRunWeightQ (endpointMeanCutoff 27 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 27 22) = (412833263/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 27 22 h = (logRoundedQ ((endpointMeanCutoff 27 22:ℚ)/200)).2+(412833263/1000000000000000:ℚ)+((endpointMeanRuns 27 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 27 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 27 22) r*endpointJoint24Q (endpointMeanCornerK 27 22 h) (endpointMeanCornerA 27 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 27 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 27 22 h≤endpointMeanCorner 27 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 27 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint27_22

namespace EndpointAnalyticJoint27_23
private noncomputable def weights : IntegerLookupTree := (.branch 1407 (.branch 860 (.leaf (36195630000000:ℤ)) (.branch 1209 (.leaf (39254125700000:ℤ)) (.leaf (10895212000000:ℤ)))) (.branch 1842 (.leaf (14239819000000:ℤ)) (.branch 2975 (.leaf (10240111400000:ℤ)) (.leaf (1466509500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 126 (.leaf (1975332457376733:ℤ)) (.branch 142 (.leaf (2276429122652935:ℤ)) (.leaf (2638238673905277:ℤ)))) (.branch 164 (.leaf (3010476894422988:ℤ)) (.branch 190 (.leaf (3323709464305158:ℤ)) (.leaf (4628935655878960:ℤ))))), (.branch 155 (.branch 126 (.leaf (1987024539321077:ℤ)) (.branch 142 (.leaf (2295572582335987:ℤ)) (.leaf (2668244384611839:ℤ)))) (.branch 164 (.leaf (3053596807421606:ℤ)) (.branch 190 (.leaf (3379237955746346:ℤ)) (.leaf (4747629900883926:ℤ))))), (.branch 155 (.branch 126 (.leaf (1985504453239234:ℤ)) (.branch 142 (.leaf (2294977128578545:ℤ)) (.leaf (2670668670348883:ℤ)))) (.branch 164 (.leaf (3061777437647939:ℤ)) (.branch 190 (.leaf (3394645926771366:ℤ)) (.leaf (4820771883035019:ℤ))))), (.branch 155 (.branch 126 (.leaf (1997702815434688:ℤ)) (.branch 142 (.leaf (2315093231100948:ℤ)) (.leaf (2702478366357523:ℤ)))) (.branch 164 (.leaf (3107914554918733:ℤ)) (.branch 190 (.leaf (3454529941122037:ℤ)) (.leaf (4953122304830528:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 27 23) 8000 (endpointMeanRuns 27 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 27 23, EndpointRunConditions (endpointMeanCutoff 27 23) (endpointMeanBox 27 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 27 23 h) (endpointMeanCornerA 27 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 23, endpointJoint24Q (endpointMeanCornerK 27 23 h) (endpointMeanCornerA 27 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 27 23, endpointRunWeightQ (endpointMeanCutoff 27 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 27 23) = (102892801/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 27 23 h = (logRoundedQ ((endpointMeanCutoff 27 23:ℚ)/200)).2+(102892801/250000000000000:ℚ)+((endpointMeanRuns 27 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 27 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 27 23) r*endpointJoint24Q (endpointMeanCornerK 27 23 h) (endpointMeanCornerA 27 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 27 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 27 23 h≤endpointMeanCorner 27 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 27 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint27_23

namespace EndpointAnalyticJoint27_24
private noncomputable def weights : IntegerLookupTree := (.branch 1407 (.branch 992 (.leaf (57453962700000:ℤ)) (.leaf (34666583000000:ℤ))) (.branch 1842 (.leaf (14158166800000:ℤ)) (.branch 2975 (.leaf (10189422800000:ℤ)) (.leaf (1460494700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 126 (.leaf (1987024539321077:ℤ)) (.leaf (2295572582335987:ℤ))) (.branch 155 (.leaf (2668244384611839:ℤ)) (.branch 178 (.leaf (3053596807421606:ℤ)) (.leaf (4018144203669266:ℤ))))), (.branch 142 (.branch 126 (.leaf (1998785827226002:ℤ)) (.leaf (2314877027505030:ℤ))) (.branch 155 (.leaf (2698591361892919:ℤ)) (.branch 178 (.leaf (3097334339143835:ℤ)) (.leaf (4102873827176561:ℤ))))), (.branch 142 (.branch 126 (.leaf (1997702815434688:ℤ)) (.leaf (2315093231100948:ℤ))) (.branch 155 (.leaf (2702478366357523:ℤ)) (.branch 178 (.leaf (3107914554918733:ℤ)) (.leaf (4145609905460196:ℤ))))), (.branch 142 (.branch 126 (.leaf (2009976120821533:ℤ)) (.leaf (2335385656766465:ℤ))) (.branch 155 (.leaf (2734666940050020:ℤ)) (.branch 178 (.leaf (3154746900250162:ℤ)) (.leaf (4238539137740863:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 27 24) 8000 (endpointMeanRuns 27 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 27 24, EndpointRunConditions (endpointMeanCutoff 27 24) (endpointMeanBox 27 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 27 24 h) (endpointMeanCornerA 27 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 27 24, endpointJoint24Q (endpointMeanCornerK 27 24 h) (endpointMeanCornerA 27 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 27 24, endpointRunWeightQ (endpointMeanCutoff 27 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 27 24) = (25645177/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 27 24 h = (logRoundedQ ((endpointMeanCutoff 27 24:ℚ)/200)).2+(25645177/62500000000000:ℚ)+((endpointMeanRuns 27 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 27 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 27 24) r*endpointJoint24Q (endpointMeanCornerK 27 24 h) (endpointMeanCornerA 27 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 27 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 27 24 h≤endpointMeanCorner 27 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 27 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint27_24

namespace EndpointAnalyticJoint28_08
private noncomputable def weights : IntegerLookupTree := (.branch 1011 (.branch 758 (.leaf (47838264100000:ℤ)) (.leaf (40380007900000:ℤ))) (.branch 1804 (.leaf (66310075200000:ℤ)) (.leaf (31877232900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 175 (.branch 142 (.leaf (1818331375922832:ℤ)) (.leaf (2253086233225229:ℤ))) (.branch 200 (.leaf (2878087861520229:ℤ)) (.leaf (3584011980592927:ℤ)))), (.branch 175 (.branch 142 (.leaf (1822345163609150:ℤ)) (.leaf (2262710598667793:ℤ))) (.branch 200 (.leaf (2900011567274887:ℤ)) (.leaf (3625538961003575:ℤ)))), (.branch 175 (.branch 142 (.leaf (1822003102379952:ℤ)) (.leaf (2264180766788266:ℤ))) (.branch 200 (.leaf (2911581751429609:ℤ)) (.leaf (3667479333995007:ℤ)))), (.branch 175 (.branch 142 (.leaf (1826178482501917:ℤ)) (.leaf (2274317959703979:ℤ))) (.branch 200 (.leaf (2935175296743554:ℤ)) (.leaf (3713533890153201:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 28 8) 8000 (endpointMeanRuns 28 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 28 8, EndpointRunConditions (endpointMeanCutoff 28 8) (endpointMeanBox 28 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 28 8 h) (endpointMeanCornerA 28 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 8, endpointJoint24Q (endpointMeanCornerK 28 8 h) (endpointMeanCornerA 28 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 28 8, endpointRunWeightQ (endpointMeanCutoff 28 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 28 8) = (214897831/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 28 8 h = (logRoundedQ ((endpointMeanCutoff 28 8:ℚ)/200)).2+(214897831/500000000000000:ℚ)+((endpointMeanRuns 28 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 28 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 28 8) r*endpointJoint24Q (endpointMeanCornerK 28 8 h) (endpointMeanCornerA 28 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 28 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 28 8 h≤endpointMeanCorner 28 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 28 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint28_08

namespace EndpointAnalyticJoint28_09
private noncomputable def weights : IntegerLookupTree := (.branch 1011 (.branch 758 (.leaf (45870510400000:ℤ)) (.leaf (40126745600000:ℤ))) (.branch 1804 (.leaf (65976671400000:ℤ)) (.leaf (31754756000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 175 (.branch 142 (.leaf (1822345163609150:ℤ)) (.leaf (2262710598667793:ℤ))) (.branch 200 (.leaf (2900011567274887:ℤ)) (.leaf (3625538961003575:ℤ)))), (.branch 175 (.branch 142 (.leaf (1833541122557807:ℤ)) (.leaf (2289661203622376:ℤ))) (.branch 200 (.leaf (2961790960734501:ℤ)) (.leaf (3743433672975173:ℤ)))), (.branch 175 (.branch 142 (.leaf (1826178482501917:ℤ)) (.leaf (2274317959703979:ℤ))) (.branch 200 (.leaf (2935175296743554:ℤ)) (.leaf (3713533890153201:ℤ)))), (.branch 175 (.branch 142 (.leaf (1837827033812294:ℤ)) (.leaf (2302715599025994:ℤ))) (.branch 200 (.leaf (3001720886764173:ℤ)) (.leaf (3844520309039412:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 28 9) 8000 (endpointMeanRuns 28 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 28 9, EndpointRunConditions (endpointMeanCutoff 28 9) (endpointMeanBox 28 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 28 9 h) (endpointMeanCornerA 28 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 9, endpointJoint24Q (endpointMeanCornerK 28 9 h) (endpointMeanCornerA 28 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 28 9, endpointRunWeightQ (endpointMeanCutoff 28 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 28 9) = (428750091/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 28 9 h = (logRoundedQ ((endpointMeanCutoff 28 9:ℚ)/200)).2+(428750091/1000000000000000:ℚ)+((endpointMeanRuns 28 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 28 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 28 9) r*endpointJoint24Q (endpointMeanCornerK 28 9 h) (endpointMeanCornerA 28 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 28 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 28 9 h≤endpointMeanCorner 28 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 28 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint28_09

namespace EndpointAnalyticJoint28_10
private noncomputable def weights : IntegerLookupTree := (.branch 1011 (.branch 758 (.leaf (43210927100000:ℤ)) (.leaf (39775999100000:ℤ))) (.branch 1804 (.leaf (65514935800000:ℤ)) (.leaf (31585135900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 175 (.branch 142 (.leaf (1833541122557807:ℤ)) (.leaf (2289661203622376:ℤ))) (.branch 200 (.leaf (2961790960734501:ℤ)) (.leaf (3743433672975173:ℤ)))), (.branch 175 (.branch 142 (.leaf (1844805866223695:ℤ)) (.leaf (2316932810789009:ℤ))) (.branch 200 (.leaf (3024886450136388:ℤ)) (.leaf (3865162066851815:ℤ)))), (.branch 175 (.branch 142 (.leaf (1837827033812294:ℤ)) (.leaf (2302715599025994:ℤ))) (.branch 200 (.leaf (3001720886764173:ℤ)) (.leaf (3844520309039412:ℤ)))), (.branch 175 (.branch 142 (.leaf (1849549887141303:ℤ)) (.leaf (2331467817581584:ℤ))) (.branch 200 (.leaf (3069775182433856:ℤ)) (.leaf (3980126974418630:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 28 10) 8000 (endpointMeanRuns 28 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 28 10, EndpointRunConditions (endpointMeanCutoff 28 10) (endpointMeanBox 28 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 28 10 h) (endpointMeanCornerA 28 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 10, endpointJoint24Q (endpointMeanCornerK 28 10 h) (endpointMeanCornerA 28 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 28 10, endpointRunWeightQ (endpointMeanCutoff 28 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 28 10) = (26706379/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 28 10 h = (logRoundedQ ((endpointMeanCutoff 28 10:ℚ)/200)).2+(26706379/62500000000000:ℚ)+((endpointMeanRuns 28 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 28 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 28 10) r*endpointJoint24Q (endpointMeanCornerK 28 10 h) (endpointMeanCornerA 28 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 28 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 28 10 h≤endpointMeanCorner 28 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 28 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint28_10

namespace EndpointAnalyticJoint28_11
private noncomputable def weights : IntegerLookupTree := (.branch 1330 (.branch 1011 (.leaf (99984903500000:ℤ)) (.leaf (29201605700000:ℤ))) (.branch 1804 (.leaf (20172112800000:ℤ)) (.branch 2914 (.leaf (12060906400000:ℤ)) (.leaf (1799725300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 126 (.leaf (1844805866223695:ℤ)) (.leaf (2066792519438529:ℤ))) (.branch 157 (.leaf (2316932810789009:ℤ)) (.branch 175 (.leaf (2599687445676505:ℤ)) (.leaf (3024886450136388:ℤ))))), (.branch 142 (.branch 126 (.leaf (1856139817200123:ℤ)) (.leaf (2084908521422093:ℤ))) (.branch 157 (.leaf (2344529243548307:ℤ)) (.branch 175 (.leaf (2640270399396760:ℤ)) (.leaf (3089326072475288:ℤ))))), (.branch 142 (.branch 126 (.leaf (1849549887141303:ℤ)) (.leaf (2075288944690027:ℤ))) (.branch 157 (.leaf (2331467817581584:ℤ)) (.branch 175 (.leaf (2623764178500332:ℤ)) (.leaf (3069775182433856:ℤ))))), (.branch 142 (.branch 126 (.leaf (1861347516435428:ℤ)) (.leaf (2094260337762372:ℤ))) (.branch 157 (.leaf (2360579042725845:ℤ)) (.branch 175 (.leaf (2666957147797967:ℤ)) (.leaf (3139372388765061:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 28 11) 8000 (endpointMeanRuns 28 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 28 11, EndpointRunConditions (endpointMeanCutoff 28 11) (endpointMeanBox 28 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 28 11 h) (endpointMeanCornerA 28 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 11, endpointJoint24Q (endpointMeanCornerK 28 11 h) (endpointMeanCornerA 28 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 28 11, endpointRunWeightQ (endpointMeanCutoff 28 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 28 11) = (425669177/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 28 11 h = (logRoundedQ ((endpointMeanCutoff 28 11:ℚ)/200)).2+(425669177/1000000000000000:ℚ)+((endpointMeanRuns 28 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 28 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 28 11) r*endpointJoint24Q (endpointMeanCornerK 28 11 h) (endpointMeanCornerA 28 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 28 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 28 11 h≤endpointMeanCorner 28 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 28 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint28_11

namespace EndpointAnalyticJoint28_12
private noncomputable def weights : IntegerLookupTree := (.branch 1330 (.branch 1011 (.leaf (96131022500000:ℤ)) (.leaf (28990101900000:ℤ))) (.branch 1804 (.leaf (20046642200000:ℤ)) (.branch 2914 (.leaf (11996514900000:ℤ)) (.leaf (1791703100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 126 (.leaf (1856139817200123:ℤ)) (.leaf (2084908521422093:ℤ))) (.branch 157 (.leaf (2344529243548307:ℤ)) (.branch 175 (.leaf (2640270399396760:ℤ)) (.leaf (3089326072475288:ℤ))))), (.branch 142 (.branch 126 (.leaf (1867543400676690:ℤ)) (.leaf (2103183315120248:ℤ))) (.branch 157 (.leaf (2372454370820236:ℤ)) (.branch 175 (.leaf (2681486881634227:ℤ)) (.leaf (3155138462022350:ℤ))))), (.branch 142 (.branch 126 (.leaf (1861347516435428:ℤ)) (.leaf (2094260337762372:ℤ))) (.branch 157 (.leaf (2360579042725845:ℤ)) (.branch 175 (.leaf (2666957147797967:ℤ)) (.leaf (3139372388765061:ℤ))))), (.branch 142 (.branch 126 (.leaf (1873220398664300:ℤ)) (.leaf (2113405159096854:ℤ))) (.branch 157 (.leaf (2390053757094788:ℤ)) (.branch 175 (.leaf (2710861169030846:ℤ)) (.leaf (3210547486258082:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 28 12) 8000 (endpointMeanRuns 28 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 28 12, EndpointRunConditions (endpointMeanCutoff 28 12) (endpointMeanBox 28 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 28 12 h) (endpointMeanCornerA 28 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 12, endpointJoint24Q (endpointMeanCornerK 28 12 h) (endpointMeanCornerA 28 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 28 12, endpointRunWeightQ (endpointMeanCutoff 28 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 28 12) = (424259157/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 28 12 h = (logRoundedQ ((endpointMeanCutoff 28 12:ℚ)/200)).2+(424259157/1000000000000000:ℚ)+((endpointMeanRuns 28 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 28 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 28 12) r*endpointJoint24Q (endpointMeanCornerK 28 12 h) (endpointMeanCornerA 28 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 28 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 28 12 h≤endpointMeanCorner 28 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 28 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint28_12

namespace EndpointAnalyticJoint28_13
private noncomputable def weights : IntegerLookupTree := (.branch 1330 (.branch 758 (.leaf (35530083400000:ℤ)) (.branch 1011 (.leaf (38701527000000:ℤ)) (.leaf (28781157500000:ℤ)))) (.branch 1804 (.leaf (19922689800000:ℤ)) (.branch 2914 (.leaf (11932902500000:ℤ)) (.leaf (1783777900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.branch 126 (.leaf (1867543400676690:ℤ)) (.branch 142 (.leaf (2103183315120248:ℤ)) (.leaf (2372454370820236:ℤ)))) (.branch 175 (.leaf (2681486881634227:ℤ)) (.branch 200 (.leaf (3155138462022350:ℤ)) (.leaf (4120622606382048:ℤ))))), (.branch 157 (.branch 126 (.leaf (1879017044455238:ℤ)) (.branch 142 (.leaf (2121618292385828:ℤ)) (.leaf (2400712107606545:ℤ)))) (.branch 175 (.leaf (2723346782215669:ℤ)) (.branch 200 (.leaf (3222352863049036:ℤ)) (.leaf (4254616371322464:ℤ))))), (.branch 157 (.branch 126 (.leaf (1873220398664300:ℤ)) (.branch 142 (.leaf (2113405159096854:ℤ)) (.leaf (2390053757094788:ℤ)))) (.branch 175 (.leaf (2710861169030846:ℤ)) (.branch 200 (.leaf (3210547486258082:ℤ)) (.leaf (4265858667534946:ℤ))))), (.branch 157 (.branch 126 (.leaf (1885169013839960:ℤ)) (.branch 142 (.leaf (2132724994099562:ℤ)) (.leaf (2419896499295639:ℤ)))) (.branch 175 (.leaf (2755487947688608:ℤ)) (.branch 200 (.leaf (3283336248482704:ℤ)) (.leaf (4416327080336226:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 28 13) 8000 (endpointMeanRuns 28 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 28 13, EndpointRunConditions (endpointMeanCutoff 28 13) (endpointMeanBox 28 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 28 13 h) (endpointMeanCornerA 28 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 13, endpointJoint24Q (endpointMeanCornerK 28 13 h) (endpointMeanCornerA 28 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 28 13, endpointRunWeightQ (endpointMeanCutoff 28 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 28 13) = (422866199/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 28 13 h = (logRoundedQ ((endpointMeanCutoff 28 13:ℚ)/200)).2+(422866199/1000000000000000:ℚ)+((endpointMeanRuns 28 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 28 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 28 13) r*endpointJoint24Q (endpointMeanCornerK 28 13 h) (endpointMeanCornerA 28 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 28 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 28 13 h≤endpointMeanCorner 28 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 28 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint28_13

namespace EndpointAnalyticJoint28_14
private noncomputable def weights : IntegerLookupTree := (.branch 1330 (.branch 758 (.leaf (32974480000000:ℤ)) (.branch 1011 (.leaf (38320852400000:ℤ)) (.leaf (28545419300000:ℤ)))) (.branch 1804 (.leaf (19782842500000:ℤ)) (.branch 2914 (.leaf (11861132900000:ℤ)) (.leaf (1774836500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.branch 126 (.leaf (1879017044455238:ℤ)) (.branch 142 (.leaf (2121618292385828:ℤ)) (.leaf (2400712107606545:ℤ)))) (.branch 175 (.leaf (2723346782215669:ℤ)) (.branch 200 (.leaf (3222352863049036:ℤ)) (.leaf (4254616371322464:ℤ))))), (.branch 157 (.branch 126 (.leaf (1890561178965890:ℤ)) (.branch 142 (.leaf (2140214857271629:ℤ)) (.leaf (2429306415539639:ℤ)))) (.branch 175 (.leaf (2765860145355026:ℤ)) (.branch 200 (.leaf (3290999142822013:ℤ)) (.leaf (4392967324668132:ℤ))))), (.branch 157 (.branch 126 (.leaf (1885169013839960:ℤ)) (.branch 142 (.leaf (2132724994099562:ℤ)) (.leaf (2419896499295639:ℤ)))) (.branch 175 (.leaf (2755487947688608:ℤ)) (.branch 200 (.leaf (3283336248482704:ℤ)) (.leaf (4416327080336226:ℤ))))), (.branch 157 (.branch 126 (.leaf (1897193845036286:ℤ)) (.branch 142 (.leaf (2152221442669680:ℤ)) (.leaf (2450111864605662:ℤ)))) (.branch 175 (.leaf (2800849381959173:ℤ)) (.branch 200 (.leaf (3357775260058531:ℤ)) (.leaf (4572102922430285:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 28 14) 8000 (endpointMeanRuns 28 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 28 14, EndpointRunConditions (endpointMeanCutoff 28 14) (endpointMeanBox 28 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 28 14 h) (endpointMeanCornerA 28 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 14, endpointJoint24Q (endpointMeanCornerK 28 14 h) (endpointMeanCornerA 28 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 28 14, endpointRunWeightQ (endpointMeanCutoff 28 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 28 14) = (421294617/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 28 14 h = (logRoundedQ ((endpointMeanCutoff 28 14:ℚ)/200)).2+(421294617/1000000000000000:ℚ)+((endpointMeanRuns 28 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 28 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 28 14) r*endpointJoint24Q (endpointMeanCornerK 28 14 h) (endpointMeanCornerA 28 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 28 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 28 14 h≤endpointMeanCorner 28 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 28 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint28_14

namespace EndpointAnalyticJoint28_15
private noncomputable def weights : IntegerLookupTree := (.branch 1011 (.branch 758 (.leaf (30835024800000:ℤ)) (.branch 852 (.leaf (13721947300000:ℤ)) (.leaf (19828728500000:ℤ)))) (.branch 1804 (.branch 1330 (.leaf (28341755800000:ℤ)) (.leaf (19662022900000:ℤ))) (.branch 2914 (.leaf (11799128300000:ℤ)) (.leaf (1767111700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.branch 126 (.leaf (1890561178965890:ℤ)) (.branch 142 (.leaf (2140214857271629:ℤ)) (.leaf (2429306415539639:ℤ)))) (.branch 189 (.branch 175 (.leaf (2765860145355026:ℤ)) (.leaf (3290999142822013:ℤ))) (.branch 200 (.leaf (3836471284883602:ℤ)) (.leaf (4392967324668132:ℤ))))), (.branch 157 (.branch 126 (.leaf (1902176237283218:ℤ)) (.branch 142 (.leaf (2158974426137363:ℤ)) (.leaf (2458241303437975:ℤ)))) (.branch 189 (.branch 175 (.leaf (2809037172063497:ℤ)) (.leaf (3361107804874939:ℤ))) (.branch 200 (.leaf (3940036058152734:ℤ)) (.leaf (4535817152793822:ℤ))))), (.branch 157 (.branch 126 (.leaf (1897193845036286:ℤ)) (.branch 142 (.leaf (2152221442669680:ℤ)) (.leaf (2450111864605662:ℤ)))) (.branch 189 (.branch 175 (.leaf (2800849381959173:ℤ)) (.leaf (3357775260058531:ℤ))) (.branch 200 (.leaf (3950473884988851:ℤ)) (.leaf (4572102922430285:ℤ))))), (.branch 157 (.branch 126 (.leaf (1909295378408514:ℤ)) (.branch 142 (.leaf (2171896119331978:ℤ)) (.leaf (2480704505679787:ℤ)))) (.branch 189 (.branch 175 (.leaf (2846957565900998:ℤ)) (.leaf (3433901935042861:ℤ))) (.branch 200 (.leaf (4065044047659688:ℤ)) (.leaf (4733373401252718:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 28 15) 8000 (endpointMeanRuns 28 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 28 15, EndpointRunConditions (endpointMeanCutoff 28 15) (endpointMeanBox 28 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 28 15 h) (endpointMeanCornerA 28 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 15, endpointJoint24Q (endpointMeanCornerK 28 15 h) (endpointMeanCornerA 28 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 28 15, endpointRunWeightQ (endpointMeanCutoff 28 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 28 15) = (83987373/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 28 15 h = (logRoundedQ ((endpointMeanCutoff 28 15:ℚ)/200)).2+(83987373/200000000000000:ℚ)+((endpointMeanRuns 28 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 28 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 28 15) r*endpointJoint24Q (endpointMeanCornerK 28 15 h) (endpointMeanCornerA 28 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 28 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 28 15 h≤endpointMeanCorner 28 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 28 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint28_15

namespace EndpointAnalyticJoint28_16
private noncomputable def weights : IntegerLookupTree := (.branch 1115 (.branch 852 (.leaf (48236953900000:ℤ)) (.branch 1011 (.leaf (19667406800000:ℤ)) (.leaf (9453202100000:ℤ)))) (.branch 1804 (.branch 1330 (.leaf (15492267600000:ℤ)) (.leaf (19542611700000:ℤ))) (.branch 2914 (.leaf (11737846500000:ℤ)) (.leaf (1759476900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.branch 126 (.leaf (1902176237283218:ℤ)) (.branch 142 (.leaf (2158974426137363:ℤ)) (.leaf (2458241303437975:ℤ)))) (.branch 175 (.branch 168 (.leaf (2809037172063497:ℤ)) (.leaf (3125504344122590:ℤ))) (.branch 189 (.leaf (3361107804874939:ℤ)) (.leaf (3940036058152734:ℤ))))), (.branch 157 (.branch 126 (.leaf (1913862655142477:ℤ)) (.branch 142 (.leaf (2177898427757510:ℤ)) (.leaf (2487520827868099:ℤ)))) (.branch 175 (.branch 168 (.leaf (2852888222597261:ℤ)) (.leaf (3184579926297889:ℤ))) (.branch 189 (.leaf (3432710002562956:ℤ)) (.leaf (4046396541715476:ℤ))))), (.branch 157 (.branch 126 (.leaf (1909295378408514:ℤ)) (.branch 142 (.leaf (2171896119331978:ℤ)) (.leaf (2480704505679787:ℤ)))) (.branch 175 (.branch 168 (.leaf (2846957565900998:ℤ)) (.leaf (3181743108064581:ℤ))) (.branch 189 (.leaf (3433901935042861:ℤ)) (.leaf (4065044047659688:ℤ))))), (.branch 157 (.branch 126 (.leaf (1921474103212886:ℤ)) (.branch 142 (.leaf (2191750653370516:ℤ)) (.leaf (2511679133267026:ℤ)))) (.branch 175 (.branch 168 (.leaf (2893824792667509:ℤ)) (.leaf (3245497069074012:ℤ))) (.branch 189 (.leaf (3511754535735537:ℤ)) (.leaf (4182936931238598:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 28 16) 8000 (endpointMeanRuns 28 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 28 16, EndpointRunConditions (endpointMeanCutoff 28 16) (endpointMeanBox 28 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 28 16 h) (endpointMeanCornerA 28 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 16, endpointJoint24Q (endpointMeanCornerK 28 16 h) (endpointMeanCornerA 28 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 28 16, endpointRunWeightQ (endpointMeanCutoff 28 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 28 16) = (418594941/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 28 16 h = (logRoundedQ ((endpointMeanCutoff 28 16:ℚ)/200)).2+(418594941/1000000000000000:ℚ)+((endpointMeanRuns 28 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 28 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 28 16) r*endpointJoint24Q (endpointMeanCornerK 28 16 h) (endpointMeanCornerA 28 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 28 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 28 16 h≤endpointMeanCorner 28 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 28 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint28_16

namespace EndpointAnalyticJoint28_17
private noncomputable def weights : IntegerLookupTree := (.branch 1330 (.branch 1011 (.branch 852 (.leaf (45436962200000:ℤ)) (.leaf (19485312900000:ℤ))) (.branch 1115 (.leaf (9373491600000:ℤ)) (.leaf (15371698600000:ℤ)))) (.branch 2229 (.branch 1804 (.leaf (19407824800000:ℤ)) (.leaf (5843913500000:ℤ))) (.branch 2914 (.leaf (3000564200000:ℤ)) (.leaf (1750859100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.branch 134 (.branch 126 (.leaf (1913862655142477:ℤ)) (.leaf (2177898427757510:ℤ))) (.branch 142 (.leaf (2324019459651860:ℤ)) (.leaf (2487520827868099:ℤ)))) (.branch 175 (.branch 168 (.leaf (2852888222597261:ℤ)) (.leaf (3184579926297889:ℤ))) (.branch 189 (.leaf (3432710002562956:ℤ)) (.leaf (4046396541715476:ℤ))))), (.branch 157 (.branch 134 (.branch 126 (.leaf (1925620870955940:ℤ)) (.leaf (2196988303430171:ℤ))) (.branch 142 (.leaf (2347831708015350:ℤ)) (.leaf (2517149093713335:ℤ)))) (.branch 175 (.branch 168 (.leaf (2897423818943384:ℤ)) (.leaf (3244772104076684:ℤ))) (.branch 189 (.leaf (3505837552905918:ℤ)) (.leaf (4155628205210773:ℤ))))), (.branch 157 (.branch 134 (.branch 126 (.leaf (1921474103212886:ℤ)) (.leaf (2191750653370516:ℤ))) (.branch 142 (.leaf (2342312713585276:ℤ)) (.leaf (2511679133267026:ℤ)))) (.branch 175 (.branch 168 (.leaf (2893824792667509:ℤ)) (.leaf (3245497069074012:ℤ))) (.branch 189 (.leaf (3511754535735537:ℤ)) (.leaf (4182936931238598:ℤ))))), (.branch 157 (.branch 134 (.branch 126 (.leaf (1933730511826448:ℤ)) (.leaf (2211786688963560:ℤ))) (.branch 142 (.leaf (2367404015736973:ℤ)) (.leaf (2543040516935839:ℤ)))) (.branch 175 (.branch 168 (.leaf (2941463557784680:ℤ)) (.leaf (3310528495738690:ℤ))) (.branch 189 (.leaf (3591372191910070:ℤ)) (.leaf (4304248900031738:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 28 17) 8000 (endpointMeanRuns 28 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 28 17, EndpointRunConditions (endpointMeanCutoff 28 17) (endpointMeanBox 28 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 28 17 h) (endpointMeanCornerA 28 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 17, endpointJoint24Q (endpointMeanCornerK 28 17 h) (endpointMeanCornerA 28 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 28 17, endpointRunWeightQ (endpointMeanCutoff 28 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 28 17) = (417080227/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 28 17 h = (logRoundedQ ((endpointMeanCutoff 28 17:ℚ)/200)).2+(417080227/1000000000000000:ℚ)+((endpointMeanRuns 28 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 28 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 28 17) r*endpointJoint24Q (endpointMeanCornerK 28 17 h) (endpointMeanCornerA 28 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 28 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 28 17 h≤endpointMeanCorner 28 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 28 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint28_17

namespace EndpointAnalyticJoint28_18
private noncomputable def weights : IntegerLookupTree := (.branch 1330 (.branch 1011 (.branch 852 (.leaf (43085394200000:ℤ)) (.leaf (19327922800000:ℤ))) (.branch 1115 (.leaf (9304594900000:ℤ)) (.leaf (15267486600000:ℤ)))) (.branch 2229 (.branch 1804 (.leaf (19291323800000:ℤ)) (.leaf (5813224000000:ℤ))) (.branch 2914 (.leaf (2986267800000:ℤ)) (.leaf (1743410300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.branch 134 (.branch 126 (.leaf (1925620870955940:ℤ)) (.leaf (2196988303430171:ℤ))) (.branch 142 (.leaf (2347831708015350:ℤ)) (.leaf (2517149093713335:ℤ)))) (.branch 175 (.branch 168 (.leaf (2897423818943384:ℤ)) (.leaf (3244772104076684:ℤ))) (.branch 189 (.leaf (3505837552905918:ℤ)) (.leaf (4155628205210773:ℤ))))), (.branch 157 (.branch 134 (.branch 126 (.leaf (1937451325829372:ℤ)) (.leaf (2216245507086790:ℤ))) (.branch 142 (.leaf (2371887940210287:ℤ)) (.leaf (2547130254749304:ℤ)))) (.branch 175 (.branch 168 (.leaf (2942654647344589:ℤ)) (.leaf (3306101982384150:ℤ))) (.branch 189 (.leaf (3580522950726592:ℤ)) (.leaf (4267808555565340:ℤ))))), (.branch 157 (.branch 134 (.branch 126 (.leaf (1933730511826448:ℤ)) (.leaf (2211786688963560:ℤ))) (.branch 142 (.leaf (2367404015736973:ℤ)) (.leaf (2543040516935839:ℤ)))) (.branch 175 (.branch 168 (.leaf (2941463557784680:ℤ)) (.leaf (3310528495738690:ℤ))) (.branch 189 (.leaf (3591372191910070:ℤ)) (.leaf (4304248900031738:ℤ))))), (.branch 157 (.branch 134 (.branch 126 (.leaf (1946065099766937:ℤ)) (.leaf (2232005885319752:ℤ))) (.branch 142 (.leaf (2392764100720282:ℤ)) (.leaf (2574793485808591:ℤ)))) (.branch 175 (.branch 168 (.leaf (2989886562482501:ℤ)) (.leaf (3376862985189764:ℤ))) (.branch 189 (.leaf (3672794920480815:ℤ)) (.leaf (4429079113066757:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 28 18) 8000 (endpointMeanRuns 28 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 28 18, EndpointRunConditions (endpointMeanCutoff 28 18) (endpointMeanBox 28 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 28 18 h) (endpointMeanCornerA 28 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 18, endpointJoint24Q (endpointMeanCornerK 28 18 h) (endpointMeanCornerA 28 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 28 18, endpointRunWeightQ (endpointMeanCutoff 28 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 28 18) = (415771007/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 28 18 h = (logRoundedQ ((endpointMeanCutoff 28 18:ℚ)/200)).2+(415771007/1000000000000000:ℚ)+((endpointMeanRuns 28 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 28 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 28 18) r*endpointJoint24Q (endpointMeanCornerK 28 18 h) (endpointMeanCornerA 28 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 28 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 28 18 h≤endpointMeanCorner 28 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 28 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint28_18

namespace EndpointAnalyticJoint28_19
private noncomputable def weights : IntegerLookupTree := (.branch 1330 (.branch 1011 (.branch 852 (.leaf (40822100000000:ℤ)) (.leaf (19172302600000:ℤ))) (.branch 1115 (.leaf (9236473100000:ℤ)) (.leaf (15164446500000:ℤ)))) (.branch 2229 (.branch 1804 (.leaf (19176132900000:ℤ)) (.leaf (5782879500000:ℤ))) (.branch 2914 (.leaf (2972132300000:ℤ)) (.leaf (1736045400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.branch 134 (.branch 126 (.leaf (1937451325829372:ℤ)) (.leaf (2216245507086790:ℤ))) (.branch 142 (.leaf (2371887940210287:ℤ)) (.leaf (2547130254749304:ℤ)))) (.branch 175 (.branch 168 (.leaf (2942654647344589:ℤ)) (.leaf (3306101982384150:ℤ))) (.branch 189 (.leaf (3580522950726592:ℤ)) (.leaf (4267808555565340:ℤ))))), (.branch 157 (.branch 134 (.branch 126 (.leaf (1949354463578558:ℤ)) (.leaf (2235671505402944:ℤ))) (.branch 142 (.leaf (2396190656131228:ℤ)) (.leaf (2577468514226246:ℤ)))) (.branch 175 (.branch 168 (.leaf (2988591560863363:ℤ)) (.leaf (3368591065052527:ℤ))) (.branch 189 (.leaf (3656799383089918:ℤ)) (.leaf (4383017191989844:ℤ))))), (.branch 157 (.branch 134 (.branch 126 (.leaf (1946065099766937:ℤ)) (.leaf (2232005885319752:ℤ))) (.branch 142 (.leaf (2392764100720282:ℤ)) (.leaf (2574793485808591:ℤ)))) (.branch 175 (.branch 168 (.leaf (2989886562482501:ℤ)) (.leaf (3376862985189764:ℤ))) (.branch 189 (.leaf (3672794920480815:ℤ)) (.leaf (4429079113066757:ℤ))))), (.branch 157 (.branch 134 (.branch 126 (.leaf (1958478365712837:ℤ)) (.leaf (2252409916815481:ℤ))) (.branch 142 (.leaf (2418395847788337:ℤ)) (.leaf (2606942929305130:ℤ)))) (.branch 175 (.branch 168 (.leaf (3039106717081354:ℤ)) (.leaf (3444526647459128:ℤ))) (.branch 189 (.leaf (3756063645616006:ℤ)) (.leaf (4557529605144243:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 28 19) 8000 (endpointMeanRuns 28 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 28 19, EndpointRunConditions (endpointMeanCutoff 28 19) (endpointMeanBox 28 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 28 19 h) (endpointMeanCornerA 28 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 19, endpointJoint24Q (endpointMeanCornerK 28 19 h) (endpointMeanCornerA 28 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 28 19, endpointRunWeightQ (endpointMeanCutoff 28 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 28 19) = (414476509/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 28 19 h = (logRoundedQ ((endpointMeanCutoff 28 19:ℚ)/200)).2+(414476509/1000000000000000:ℚ)+((endpointMeanRuns 28 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 28 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 28 19) r*endpointJoint24Q (endpointMeanCornerK 28 19 h) (endpointMeanCornerA 28 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 28 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 28 19 h≤endpointMeanCorner 28 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 28 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint28_19

namespace EndpointAnalyticJoint28_20
private noncomputable def weights : IntegerLookupTree := (.branch 1115 (.branch 790 (.leaf (26987104700000:ℤ)) (.branch 936 (.leaf (19526345400000:ℤ)) (.leaf (18214485900000:ℤ)))) (.branch 1804 (.branch 1330 (.leaf (15062552100000:ℤ)) (.leaf (19062222900000:ℤ))) (.branch 2914 (.leaf (11491311000000:ℤ)) (.leaf (1728762300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.branch 126 (.leaf (1949354463578558:ℤ)) (.branch 142 (.leaf (2235671505402944:ℤ)) (.leaf (2577468514226246:ℤ)))) (.branch 181 (.branch 168 (.leaf (2988591560863363:ℤ)) (.leaf (3368591065052527:ℤ))) (.branch 196 (.leaf (3940108940062326:ℤ)) (.leaf (4848306674836476:ℤ))))), (.branch 157 (.branch 126 (.leaf (1961330730745962:ℤ)) (.branch 142 (.leaf (2255267777910008:ℤ)) (.leaf (2608168125458312:ℤ)))) (.branch 181 (.branch 168 (.leaf (3035245581986165:ℤ)) (.leaf (3432261262360909:ℤ))) (.branch 196 (.leaf (4033033374958802:ℤ)) (.leaf (4995617259873764:ℤ))))), (.branch 157 (.branch 126 (.leaf (1958478365712837:ℤ)) (.branch 142 (.leaf (2252409916815481:ℤ)) (.leaf (2606942929305130:ℤ)))) (.branch 181 (.branch 168 (.leaf (3039106717081354:ℤ)) (.leaf (3444526647459128:ℤ))) (.branch 196 (.leaf (4065859303320450:ℤ)) (.leaf (5084140137537389:ℤ))))), (.branch 157 (.branch 126 (.leaf (1970970811523507:ℤ)) (.branch 142 (.leaf (2273000473133575:ℤ)) (.leaf (2639493797895694:ℤ)))) (.branch 181 (.branch 168 (.leaf (3089137144434075:ℤ)) (.leaf (3513546115756688:ℤ))) (.branch 196 (.leaf (4168292030768035:ℤ)) (.leaf (5251071826742921:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 28 20) 8000 (endpointMeanRuns 28 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 28 20, EndpointRunConditions (endpointMeanCutoff 28 20) (endpointMeanBox 28 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 28 20 h) (endpointMeanCornerA 28 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 20, endpointJoint24Q (endpointMeanCornerK 28 20 h) (endpointMeanCornerA 28 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 28 20, endpointRunWeightQ (endpointMeanCutoff 28 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 28 20) = (413196407/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 28 20 h = (logRoundedQ ((endpointMeanCutoff 28 20:ℚ)/200)).2+(413196407/1000000000000000:ℚ)+((endpointMeanRuns 28 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 28 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 28 20) r*endpointJoint24Q (endpointMeanCornerK 28 20 h) (endpointMeanCornerA 28 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 28 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 28 20 h≤endpointMeanCorner 28 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 28 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint28_20

namespace EndpointAnalyticJoint28_21
private noncomputable def weights : IntegerLookupTree := (.branch 1115 (.branch 790 (.leaf (24925813900000:ℤ)) (.branch 936 (.leaf (19337476100000:ℤ)) (.leaf (18058805600000:ℤ)))) (.branch 1804 (.branch 1330 (.leaf (14947472300000:ℤ)) (.leaf (18933572500000:ℤ))) (.branch 2914 (.leaf (11425287600000:ℤ)) (.leaf (1720536800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.branch 126 (.leaf (1961330730745962:ℤ)) (.branch 142 (.leaf (2255267777910008:ℤ)) (.leaf (2608168125458312:ℤ)))) (.branch 181 (.branch 168 (.leaf (3035245581986165:ℤ)) (.leaf (3432261262360909:ℤ))) (.branch 196 (.leaf (4033033374958802:ℤ)) (.leaf (4995617259873764:ℤ))))), (.branch 157 (.branch 126 (.leaf (1973380576617463:ℤ)) (.branch 142 (.leaf (2275035817107860:ℤ)) (.leaf (2639233392419869:ℤ)))) (.branch 181 (.branch 168 (.leaf (3082627905268230:ℤ)) (.leaf (3497134898717550:ℤ))) (.branch 196 (.leaf (4128149361087033:ℤ)) (.leaf (5147403718637569:ℤ))))), (.branch 157 (.branch 126 (.leaf (1970970811523507:ℤ)) (.branch 142 (.leaf (2273000473133575:ℤ)) (.leaf (2639493797895694:ℤ)))) (.branch 181 (.branch 168 (.leaf (3089137144434075:ℤ)) (.leaf (3513546115756688:ℤ))) (.branch 196 (.leaf (4168292030768035:ℤ)) (.leaf (5251071826742921:ℤ))))), (.branch 157 (.branch 126 (.leaf (1983542942259509:ℤ)) (.branch 142 (.leaf (2293779259403209:ℤ)) (.leaf (2672451103863193:ℤ)))) (.branch 181 (.branch 168 (.leaf (3139991183424722:ℤ)) (.leaf (3583948556953471:ℤ))) (.branch 196 (.leaf (4273305384565330:ℤ)) (.leaf (5423484519246389:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 28 21) 8000 (endpointMeanRuns 28 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 28 21, EndpointRunConditions (endpointMeanCutoff 28 21) (endpointMeanBox 28 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 28 21 h) (endpointMeanCornerA 28 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 21, endpointJoint24Q (endpointMeanCornerK 28 21 h) (endpointMeanCornerA 28 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 28 21, endpointRunWeightQ (endpointMeanCutoff 28 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 28 21) = (411750653/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 28 21 h = (logRoundedQ ((endpointMeanCutoff 28 21:ℚ)/200)).2+(411750653/1000000000000000:ℚ)+((endpointMeanRuns 28 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 28 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 28 21) r*endpointJoint24Q (endpointMeanCornerK 28 21 h) (endpointMeanCornerA 28 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 28 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 28 21 h≤endpointMeanCorner 28 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 28 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint28_21

namespace EndpointAnalyticJoint28_22
private noncomputable def weights : IntegerLookupTree := (.branch 1330 (.branch 936 (.leaf (49480991600000:ℤ)) (.branch 1115 (.leaf (17924171000000:ℤ)) (.leaf (14847949500000:ℤ)))) (.branch 1804 (.leaf (18822313700000:ℤ)) (.branch 2914 (.leaf (11368189500000:ℤ)) (.leaf (1713423300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.branch 126 (.leaf (1973380576617463:ℤ)) (.branch 142 (.leaf (2275035817107860:ℤ)) (.leaf (2639233392419869:ℤ)))) (.branch 168 (.leaf (3082627905268230:ℤ)) (.branch 181 (.leaf (3497134898717550:ℤ)) (.leaf (4128149361087033:ℤ))))), (.branch 157 (.branch 126 (.leaf (1985504453239234:ℤ)) (.branch 142 (.leaf (2294977128578545:ℤ)) (.leaf (2670668670348883:ℤ)))) (.branch 168 (.leaf (3130749900019686:ℤ)) (.branch 181 (.leaf (3563234720487364:ℤ)) (.leaf (4225508584494998:ℤ))))), (.branch 157 (.branch 126 (.leaf (1983542942259509:ℤ)) (.branch 142 (.leaf (2293779259403209:ℤ)) (.leaf (2672451103863193:ℤ)))) (.branch 168 (.leaf (3139991183424722:ℤ)) (.branch 181 (.leaf (3583948556953471:ℤ)) (.leaf (4273305384565330:ℤ))))), (.branch 157 (.branch 126 (.leaf (1996195266203002:ℤ)) (.branch 142 (.leaf (2314747996341107:ℤ)) (.leaf (2705819922075008:ℤ)))) (.branch 168 (.leaf (3191682392524933:ℤ)) (.branch 181 (.leaf (3655761682274829:ℤ)) (.leaf (4380964379405613:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 28 22) 8000 (endpointMeanRuns 28 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 28 22, EndpointRunConditions (endpointMeanCutoff 28 22) (endpointMeanBox 28 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 28 22 h) (endpointMeanCornerA 28 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 22, endpointJoint24Q (endpointMeanCornerK 28 22 h) (endpointMeanCornerA 28 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 28 22, endpointRunWeightQ (endpointMeanCutoff 28 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 28 22) = (51312543/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 28 22 h = (logRoundedQ ((endpointMeanCutoff 28 22:ℚ)/200)).2+(51312543/125000000000000:ℚ)+((endpointMeanRuns 28 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 28 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 28 22) r*endpointJoint24Q (endpointMeanCornerK 28 22 h) (endpointMeanCornerA 28 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 28 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 28 22 h≤endpointMeanCorner 28 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 28 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint28_22

namespace EndpointAnalyticJoint28_23
private noncomputable def weights : IntegerLookupTree := (.branch 1330 (.branch 936 (.leaf (47194934300000:ℤ)) (.leaf (38271839300000:ℤ))) (.branch 1804 (.leaf (18712250300000:ℤ)) (.branch 2914 (.leaf (11311705000000:ℤ)) (.leaf (1706386200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 126 (.leaf (1985504453239234:ℤ)) (.leaf (2294977128578545:ℤ))) (.branch 157 (.leaf (2670668670348883:ℤ)) (.branch 181 (.leaf (3130749900019686:ℤ)) (.leaf (4225508584494998:ℤ))))), (.branch 142 (.branch 126 (.leaf (1997702815434688:ℤ)) (.leaf (2315093231100948:ℤ))) (.branch 157 (.leaf (2702478366357523:ℤ)) (.branch 181 (.leaf (3179623113033627:ℤ)) (.leaf (4325163950206332:ℤ))))), (.branch 142 (.branch 126 (.leaf (1996195266203002:ℤ)) (.leaf (2314747996341107:ℤ))) (.branch 157 (.leaf (2705819922075008:ℤ)) (.branch 181 (.leaf (3191682392524933:ℤ)) (.leaf (4380964379405613:ℤ))))), (.branch 142 (.branch 126 (.leaf (2008928294878293:ℤ)) (.leaf (2335908420394045:ℤ))) (.branch 157 (.leaf (2739605390764451:ℤ)) (.branch 181 (.leaf (3244224553408815:ℤ)) (.leaf (4491335667921855:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 28 23) 8000 (endpointMeanRuns 28 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 28 23, EndpointRunConditions (endpointMeanCutoff 28 23) (endpointMeanBox 28 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 28 23 h) (endpointMeanCornerA 28 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 23, endpointJoint24Q (endpointMeanCornerK 28 23 h) (endpointMeanCornerA 28 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 28 23, endpointRunWeightQ (endpointMeanCutoff 28 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 28 23) = (409263469/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 28 23 h = (logRoundedQ ((endpointMeanCutoff 28 23:ℚ)/200)).2+(409263469/1000000000000000:ℚ)+((endpointMeanRuns 28 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 28 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 28 23) r*endpointJoint24Q (endpointMeanCornerK 28 23 h) (endpointMeanCornerA 28 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 28 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 28 23 h≤endpointMeanCorner 28 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 28 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint28_23

namespace EndpointAnalyticJoint28_24
private noncomputable def weights : IntegerLookupTree := (.branch 1330 (.branch 892 (.leaf (37075915800000:ℤ)) (.leaf (46033861300000:ℤ))) (.branch 1804 (.leaf (18587894800000:ℤ)) (.branch 2914 (.leaf (11247885800000:ℤ)) (.leaf (1698435300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 126 (.leaf (1997702815434688:ℤ)) (.leaf (2315093231100948:ℤ))) (.branch 157 (.leaf (2702478366357523:ℤ)) (.branch 185 (.leaf (3179623113033627:ℤ)) (.leaf (4586308248232768:ℤ))))), (.branch 142 (.branch 126 (.leaf (2009976120821533:ℤ)) (.leaf (2335385656766465:ℤ))) (.branch 157 (.leaf (2734666940050020:ℤ)) (.branch 185 (.leaf (3229259271356697:ℤ)) (.leaf (4702034114684715:ℤ))))), (.branch 142 (.branch 126 (.leaf (2008928294878293:ℤ)) (.leaf (2335908420394045:ℤ))) (.branch 157 (.leaf (2739605390764451:ℤ)) (.branch 185 (.leaf (3244224553408815:ℤ)) (.leaf (4783015949231848:ℤ))))), (.branch 142 (.branch 126 (.leaf (2021742543072531:ℤ)) (.leaf (2357262283882642:ℤ))) (.branch 157 (.leaf (2773812712321940:ℤ)) (.branch 185 (.leaf (3297631674627348:ℤ)) (.leaf (4912293480546538:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 28 24) 8000 (endpointMeanRuns 28 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 28 24, EndpointRunConditions (endpointMeanCutoff 28 24) (endpointMeanBox 28 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 28 24 h) (endpointMeanCornerA 28 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 28 24, endpointJoint24Q (endpointMeanCornerK 28 24 h) (endpointMeanCornerA 28 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 28 24, endpointRunWeightQ (endpointMeanCutoff 28 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 28 24) = (203932991/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 28 24 h = (logRoundedQ ((endpointMeanCutoff 28 24:ℚ)/200)).2+(203932991/500000000000000:ℚ)+((endpointMeanRuns 28 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 28 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 28 24) r*endpointJoint24Q (endpointMeanCornerK 28 24 h) (endpointMeanCornerA 28 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 28 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 28 24 h≤endpointMeanCorner 28 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 28 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint28_24

namespace EndpointAnalyticJoint29_09
private noncomputable def weights : IntegerLookupTree := (.branch 1281 (.branch 929 (.leaf (84158518200000:ℤ)) (.leaf (39594296900000:ℤ))) (.branch 1954 (.leaf (31051576500000:ℤ)) (.leaf (21504131400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 158 (.branch 138 (.leaf (1828401451923156:ℤ)) (.leaf (2216108793324019:ℤ))) (.branch 180 (.leaf (2567125374484460:ℤ)) (.leaf (3079469380128396:ℤ)))), (.branch 158 (.branch 138 (.leaf (1837827033812294:ℤ)) (.leaf (2236824476333957:ℤ))) (.branch 180 (.leaf (2601866916149581:ℤ)) (.leaf (3140970758344782:ℤ)))), (.branch 158 (.branch 138 (.leaf (1832515765341885:ℤ)) (.leaf (2227305517701536:ℤ))) (.branch 180 (.leaf (2589396922959440:ℤ)) (.leaf (3128722346330840:ℤ)))), (.branch 158 (.branch 138 (.leaf (1842326853784379:ℤ)) (.leaf (2249122913165167:ℤ))) (.branch 180 (.leaf (2626435234151311:ℤ)) (.leaf (3195665567102521:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 29 9) 8000 (endpointMeanRuns 29 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 29 9, EndpointRunConditions (endpointMeanCutoff 29 9) (endpointMeanBox 29 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 29 9 h) (endpointMeanCornerA 29 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 9, endpointJoint24Q (endpointMeanCornerK 29 9 h) (endpointMeanCornerA 29 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 29 9, endpointRunWeightQ (endpointMeanCutoff 29 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 29 9) = (13314851/31250000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 29 9 h = (logRoundedQ ((endpointMeanCutoff 29 9:ℚ)/200)).2+(13314851/31250000000000:ℚ)+((endpointMeanRuns 29 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 29 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 29 9) r*endpointJoint24Q (endpointMeanCornerK 29 9 h) (endpointMeanCornerA 29 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 29 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 29 9 h≤endpointMeanCorner 29 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 29 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint29_09

namespace EndpointAnalyticJoint29_10
private noncomputable def weights : IntegerLookupTree := (.branch 1281 (.branch 929 (.leaf (80615669900000:ℤ)) (.leaf (39295286100000:ℤ))) (.branch 1954 (.leaf (30857452800000:ℤ)) (.leaf (21393995100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 158 (.branch 138 (.leaf (1837827033812294:ℤ)) (.leaf (2236824476333957:ℤ))) (.branch 180 (.leaf (2601866916149581:ℤ)) (.leaf (3140970758344782:ℤ)))), (.branch 158 (.branch 138 (.leaf (1849549887141303:ℤ)) (.leaf (2262709382634975:ℤ))) (.branch 180 (.leaf (2645479026216618:ℤ)) (.leaf (3218724303224742:ℤ)))), (.branch 158 (.branch 138 (.leaf (1842326853784379:ℤ)) (.leaf (2249122913165167:ℤ))) (.branch 180 (.leaf (2626435234151311:ℤ)) (.leaf (3195665567102521:ℤ)))), (.branch 158 (.branch 138 (.leaf (1854531871543252:ℤ)) (.leaf (2276397970556209:ℤ))) (.branch 180 (.leaf (2672970104230873:ℤ)) (.leaf (3280431338800027:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 29 10) 8000 (endpointMeanRuns 29 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 29 10, EndpointRunConditions (endpointMeanCutoff 29 10) (endpointMeanBox 29 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 29 10 h) (endpointMeanCornerA 29 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 10, endpointJoint24Q (endpointMeanCornerK 29 10 h) (endpointMeanCornerA 29 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 29 10, endpointRunWeightQ (endpointMeanCutoff 29 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 29 10) = (21233013/50000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 29 10 h = (logRoundedQ ((endpointMeanCutoff 29 10:ℚ)/200)).2+(21233013/50000000000000:ℚ)+((endpointMeanRuns 29 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 29 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 29 10) r*endpointJoint24Q (endpointMeanCornerK 29 10 h) (endpointMeanCornerA 29 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 29 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 29 10 h≤endpointMeanCorner 29 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 29 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint29_10

namespace EndpointAnalyticJoint29_11
private noncomputable def weights : IntegerLookupTree := (.branch 1650 (.branch 929 (.leaf (77199102600000:ℤ)) (.leaf (73874078100000:ℤ))) (.branch 2856 (.leaf (18927901900000:ℤ)) (.leaf (2078011000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 145 (.branch 126 (.leaf (1849549887141303:ℤ)) (.leaf (2075288944690027:ℤ))) (.branch 180 (.leaf (2385365469115511:ℤ)) (.leaf (3218724303224742:ℤ)))), (.branch 145 (.branch 126 (.leaf (1861347516435428:ℤ)) (.leaf (2094260337762372:ℤ))) (.branch 180 (.leaf (2416874774209573:ℤ)) (.leaf (3298402607743209:ℤ)))), (.branch 145 (.branch 126 (.leaf (1854531871543252:ℤ)) (.leaf (2084332237635584:ℤ))) (.branch 180 (.leaf (2402804333112359:ℤ)) (.leaf (3280431338800027:ℤ)))), (.branch 145 (.branch 126 (.leaf (1866817744910449:ℤ)) (.leaf (2104217902896564:ℤ))) (.branch 180 (.leaf (2436156679677603:ℤ)) (.leaf (3367445542287597:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 29 11) 8000 (endpointMeanRuns 29 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 29 11, EndpointRunConditions (endpointMeanCutoff 29 11) (endpointMeanBox 29 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 29 11 h) (endpointMeanCornerA 29 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 11, endpointJoint24Q (endpointMeanCornerK 29 11 h) (endpointMeanCornerA 29 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 29 11, endpointRunWeightQ (endpointMeanCutoff 29 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 29 11) = (42326247/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 29 11 h = (logRoundedQ ((endpointMeanCutoff 29 11:ℚ)/200)).2+(42326247/100000000000000:ℚ)+((endpointMeanRuns 29 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 29 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 29 11) r*endpointJoint24Q (endpointMeanCornerK 29 11 h) (endpointMeanCornerA 29 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 29 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 29 11 h≤endpointMeanCorner 29 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 29 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint29_11

namespace EndpointAnalyticJoint29_12
private noncomputable def weights : IntegerLookupTree := (.branch 1281 (.branch 929 (.leaf (73443175000000:ℤ)) (.leaf (38666663200000:ℤ))) (.branch 1650 (.leaf (18493674800000:ℤ)) (.branch 2856 (.leaf (18809970600000:ℤ)) (.leaf (2067502700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 145 (.branch 126 (.leaf (1861347516435428:ℤ)) (.leaf (2094260337762372:ℤ))) (.branch 158 (.leaf (2416874774209573:ℤ)) (.branch 180 (.leaf (2689822156049769:ℤ)) (.leaf (3298402607743209:ℤ))))), (.branch 145 (.branch 126 (.leaf (1873220398664300:ℤ)) (.leaf (2113405159096854:ℤ))) (.branch 158 (.leaf (2448800299090653:ℤ)) (.branch 180 (.leaf (2734908558894691:ℤ)) (.leaf (3380053318598116:ℤ))))), (.branch 145 (.branch 126 (.leaf (1866817744910449:ℤ)) (.leaf (2104217902896564:ℤ))) (.branch 158 (.leaf (2436156679677603:ℤ)) (.branch 180 (.leaf (2720329473656606:ℤ)) (.leaf (3367445542287597:ℤ))))), (.branch 145 (.branch 126 (.leaf (1879185009536926:ℤ)) (.leaf (2124293288239458:ℤ))) (.branch 158 (.leaf (2469971976557222:ℤ)) (.branch 180 (.leaf (2768527950810798:ℤ)) (.leaf (3456767817740897:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 29 12) 8000 (endpointMeanRuns 29 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 29 12, EndpointRunConditions (endpointMeanCutoff 29 12) (endpointMeanBox 29 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 29 12 h) (endpointMeanCornerA 29 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 12, endpointJoint24Q (endpointMeanCornerK 29 12 h) (endpointMeanCornerA 29 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 29 12, endpointRunWeightQ (endpointMeanCutoff 29 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 29 12) = (84337101/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 29 12 h = (logRoundedQ ((endpointMeanCutoff 29 12:ℚ)/200)).2+(84337101/200000000000000:ℚ)+((endpointMeanRuns 29 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 29 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 29 12) r*endpointJoint24Q (endpointMeanCornerK 29 12 h) (endpointMeanCornerA 29 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 29 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 29 12 h≤endpointMeanCorner 29 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 29 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint29_12

namespace EndpointAnalyticJoint29_13
private noncomputable def weights : IntegerLookupTree := (.branch 1061 (.branch 799 (.leaf (41445194000000:ℤ)) (.leaf (37667723200000:ℤ))) (.branch 1650 (.leaf (45392734700000:ℤ)) (.branch 2856 (.leaf (18708089600000:ℤ)) (.leaf (2058424600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 145 (.branch 126 (.leaf (1873220398664300:ℤ)) (.leaf (2113405159096854:ℤ))) (.branch 170 (.leaf (2448800299090653:ℤ)) (.branch 193 (.leaf (3055990506270225:ℤ)) (.leaf (3909827802824419:ℤ))))), (.branch 145 (.branch 126 (.leaf (1885169013839960:ℤ)) (.leaf (2132724994099562:ℤ))) (.branch 170 (.leaf (2481147541782604:ℤ)) (.branch 193 (.leaf (3119429735873118:ℤ)) (.leaf (4031532860812714:ℤ))))), (.branch 145 (.branch 126 (.leaf (1879185009536926:ℤ)) (.leaf (2124293288239458:ℤ))) (.branch 170 (.leaf (2469971976557222:ℤ)) (.branch 193 (.leaf (3108239680031517:ℤ)) (.leaf (4040626010889110:ℤ))))), (.branch 145 (.branch 126 (.leaf (1891634204622201:ℤ)) (.leaf (2144560203697230:ℤ))) (.branch 170 (.leaf (2504256649775648:ℤ)) (.branch 193 (.leaf (3176903722350216:ℤ)) (.leaf (4176962134875075:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 29 13) 8000 (endpointMeanRuns 29 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 29 13, EndpointRunConditions (endpointMeanCutoff 29 13) (endpointMeanBox 29 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 29 13 h) (endpointMeanCornerA 29 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 13, endpointJoint24Q (endpointMeanCornerK 29 13 h) (endpointMeanCornerA 29 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 29 13, endpointRunWeightQ (endpointMeanCutoff 29 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 29 13) = (420323163/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 29 13 h = (logRoundedQ ((endpointMeanCutoff 29 13:ℚ)/200)).2+(420323163/1000000000000000:ℚ)+((endpointMeanRuns 29 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 29 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 29 13) r*endpointJoint24Q (endpointMeanCornerK 29 13 h) (endpointMeanCornerA 29 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 29 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 29 13 h≤endpointMeanCorner 29 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 29 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint29_13

namespace EndpointAnalyticJoint29_14
private noncomputable def weights : IntegerLookupTree := (.branch 1281 (.branch 799 (.leaf (39077711600000:ℤ)) (.branch 1061 (.leaf (37356683400000:ℤ)) (.leaf (18418261500000:ℤ)))) (.branch 1650 (.leaf (18262496300000:ℤ)) (.branch 2856 (.leaf (18607400100000:ℤ)) (.leaf (2049452700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 158 (.branch 126 (.leaf (1885169013839960:ℤ)) (.branch 145 (.leaf (2132724994099562:ℤ)) (.leaf (2481147541782604:ℤ)))) (.branch 170 (.leaf (2780750693384150:ℤ)) (.branch 193 (.leaf (3119429735873118:ℤ)) (.leaf (4031532860812714:ℤ))))), (.branch 158 (.branch 126 (.leaf (1897193845036286:ℤ)) (.branch 145 (.leaf (2152221442669680:ℤ)) (.leaf (2513922072935011:ℤ)))) (.branch 170 (.leaf (2827361226980667:ℤ)) (.branch 193 (.leaf (3184185898838316:ℤ)) (.leaf (4157026351920559:ℤ))))), (.branch 158 (.branch 126 (.leaf (1891634204622201:ℤ)) (.branch 145 (.leaf (2144560203697230:ℤ)) (.leaf (2504256649775648:ℤ)))) (.branch 170 (.leaf (2817580402905337:ℤ)) (.branch 193 (.leaf (3176903722350216:ℤ)) (.leaf (4176962134875075:ℤ))))), (.branch 158 (.branch 126 (.leaf (1904165872937889:ℤ)) (.branch 145 (.leaf (2165020476571535:ℤ)) (.leaf (2539017214554319:ℤ)))) (.branch 170 (.leaf (2867501960567609:ℤ)) (.branch 193 (.leaf (3247084620250494:ℤ)) (.leaf (4317898421967805:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 29 14) 8000 (endpointMeanRuns 29 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 29 14, EndpointRunConditions (endpointMeanCutoff 29 14) (endpointMeanBox 29 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 29 14 h) (endpointMeanCornerA 29 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 14, endpointJoint24Q (endpointMeanCornerK 29 14 h) (endpointMeanCornerA 29 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 29 14, endpointRunWeightQ (endpointMeanCutoff 29 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 29 14) = (209488377/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 29 14 h = (logRoundedQ ((endpointMeanCutoff 29 14:ℚ)/200)).2+(209488377/500000000000000:ℚ)+((endpointMeanRuns 29 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 29 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 29 14) r*endpointJoint24Q (endpointMeanCornerK 29 14 h) (endpointMeanCornerA 29 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 29 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 29 14 h≤endpointMeanCorner 29 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 29 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint29_14

namespace EndpointAnalyticJoint29_15
private noncomputable def weights : IntegerLookupTree := (.branch 1281 (.branch 799 (.leaf (36484199900000:ℤ)) (.branch 1061 (.leaf (37005607600000:ℤ)) (.leaf (18270859100000:ℤ)))) (.branch 1650 (.leaf (18132796300000:ℤ)) (.branch 2856 (.leaf (18493750300000:ℤ)) (.leaf (2039326000000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 158 (.branch 126 (.leaf (1897193845036286:ℤ)) (.branch 145 (.leaf (2152221442669680:ℤ)) (.leaf (2513922072935011:ℤ)))) (.branch 170 (.leaf (2827361226980667:ℤ)) (.branch 193 (.leaf (3184185898838316:ℤ)) (.leaf (4157026351920559:ℤ))))), (.branch 158 (.branch 126 (.leaf (1909295378408514:ℤ)) (.branch 145 (.leaf (2171896119331978:ℤ)) (.leaf (2547129536782542:ℤ)))) (.branch 170 (.leaf (2874753039476916:ℤ)) (.branch 193 (.leaf (3250286333352173:ℤ)) (.leaf (4286426202434150:ℤ))))), (.branch 158 (.branch 126 (.leaf (1904165872937889:ℤ)) (.branch 145 (.leaf (2165020476571535:ℤ)) (.leaf (2539017214554319:ℤ)))) (.branch 170 (.leaf (2867501960567609:ℤ)) (.branch 193 (.leaf (3247084620250494:ℤ)) (.leaf (4317898421967805:ℤ))))), (.branch 158 (.branch 126 (.leaf (1916780560851332:ℤ)) (.branch 145 (.leaf (2185675951597483:ℤ)) (.leaf (2574260276549821:ℤ)))) (.branch 170 (.leaf (2918308022507691:ℤ)) (.branch 193 (.leaf (3318815882549744:ℤ)) (.leaf (4463590087821003:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 29 15) 8000 (endpointMeanRuns 29 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 29 15, EndpointRunConditions (endpointMeanCutoff 29 15) (endpointMeanBox 29 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 29 15 h) (endpointMeanCornerA 29 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 15, endpointJoint24Q (endpointMeanCornerK 29 15 h) (endpointMeanCornerA 29 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 29 15, endpointRunWeightQ (endpointMeanCutoff 29 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 29 15) = (417457041/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 29 15 h = (logRoundedQ ((endpointMeanCutoff 29 15:ℚ)/200)).2+(417457041/1000000000000000:ℚ)+((endpointMeanRuns 29 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 29 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 29 15) r*endpointJoint24Q (endpointMeanCornerK 29 15 h) (endpointMeanCornerA 29 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 29 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 29 15 h≤endpointMeanCorner 29 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 29 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint29_15

namespace EndpointAnalyticJoint29_16
private noncomputable def weights : IntegerLookupTree := (.branch 1281 (.branch 799 (.leaf (34309120600000:ℤ)) (.branch 1061 (.leaf (36702172800000:ℤ)) (.leaf (18143459200000:ℤ)))) (.branch 2184 (.branch 1650 (.leaf (18020696600000:ℤ)) (.leaf (10363686200000:ℤ))) (.branch 2856 (.leaf (3398754100000:ℤ)) (.leaf (2030573400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 145 (.branch 126 (.leaf (1909295378408514:ℤ)) (.branch 134 (.leaf (2171896119331978:ℤ)) (.leaf (2317487345528253:ℤ)))) (.branch 170 (.branch 158 (.leaf (2547129536782542:ℤ)) (.leaf (2874753039476916:ℤ))) (.branch 193 (.leaf (3250286333352173:ℤ)) (.leaf (4286426202434150:ℤ))))), (.branch 145 (.branch 126 (.leaf (1921474103212886:ℤ)) (.branch 134 (.leaf (2191750653370516:ℤ)) (.leaf (2342312713585276:ℤ)))) (.branch 170 (.branch 158 (.leaf (2580775652116956:ℤ)) (.leaf (2922939226554753:ℤ))) (.branch 193 (.leaf (3317758945113764:ℤ)) (.leaf (4419854009447278:ℤ))))), (.branch 145 (.branch 126 (.leaf (1916780560851332:ℤ)) (.branch 134 (.leaf (2185675951597483:ℤ)) (.leaf (2335802050389210:ℤ)))) (.branch 170 (.branch 158 (.leaf (2574260276549821:ℤ)) (.leaf (2918308022507691:ℤ))) (.branch 193 (.leaf (3318815882549744:ℤ)) (.leaf (4463590087821003:ℤ))))), (.branch 145 (.branch 126 (.leaf (1929478818349453:ℤ)) (.branch 134 (.leaf (2206528491109962:ℤ)) (.leaf (2361985385321494:ℤ)))) (.branch 170 (.branch 158 (.leaf (2609992533109145:ℤ)) (.leaf (2970014260268173:ℤ))) (.branch 193 (.leaf (3392131758307768:ℤ)) (.leaf (4614197585272071:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 29 16) 8000 (endpointMeanRuns 29 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 29 16, EndpointRunConditions (endpointMeanCutoff 29 16) (endpointMeanBox 29 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 29 16 h) (endpointMeanCornerA 29 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 16, endpointJoint24Q (endpointMeanCornerK 29 16 h) (endpointMeanCornerA 29 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 29 16, endpointRunWeightQ (endpointMeanCutoff 29 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 29 16) = (416143553/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 29 16 h = (logRoundedQ ((endpointMeanCutoff 29 16:ℚ)/200)).2+(416143553/1000000000000000:ℚ)+((endpointMeanRuns 29 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 29 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 29 16) r*endpointJoint24Q (endpointMeanCornerK 29 16 h) (endpointMeanCornerA 29 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 29 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 29 16 h≤endpointMeanCorner 29 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 29 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint29_16

namespace EndpointAnalyticJoint29_17
private noncomputable def weights : IntegerLookupTree := (.branch 1281 (.branch 799 (.leaf (31926545200000:ℤ)) (.branch 1061 (.leaf (36359577400000:ℤ)) (.leaf (17999617400000:ℤ)))) (.branch 2184 (.branch 1650 (.leaf (17894129500000:ℤ)) (.leaf (10299802200000:ℤ))) (.branch 2856 (.leaf (3380195900000:ℤ)) (.leaf (2020691300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 145 (.branch 126 (.leaf (1921474103212886:ℤ)) (.branch 134 (.leaf (2191750653370516:ℤ)) (.leaf (2342312713585276:ℤ)))) (.branch 170 (.branch 158 (.leaf (2580775652116956:ℤ)) (.leaf (2922939226554753:ℤ))) (.branch 193 (.leaf (3317758945113764:ℤ)) (.leaf (4419854009447278:ℤ))))), (.branch 145 (.branch 126 (.leaf (1933730511826448:ℤ)) (.branch 134 (.leaf (2211786688963560:ℤ)) (.leaf (2367404015736973:ℤ)))) (.branch 170 (.branch 158 (.leaf (2614866213271942:ℤ)) (.leaf (2971933103403924:ℤ))) (.branch 193 (.leaf (3386632219115844:ℤ)) (.leaf (4557435155126125:ℤ))))), (.branch 145 (.branch 126 (.leaf (1929478818349453:ℤ)) (.branch 134 (.leaf (2206528491109962:ℤ)) (.leaf (2361985385321494:ℤ)))) (.branch 170 (.branch 158 (.leaf (2609992533109145:ℤ)) (.leaf (2970014260268173:ℤ))) (.branch 193 (.leaf (3392131758307768:ℤ)) (.leaf (4614197585272071:ℤ))))), (.branch 145 (.branch 126 (.leaf (1942261199062708:ℤ)) (.branch 134 (.leaf (2227579975211554:ℤ)) (.leaf (2388462224160947:ℤ)))) (.branch 170 (.branch 158 (.leaf (2646220774542435:ℤ)) (.leaf (3022636623058199:ℤ))) (.branch 193 (.leaf (3467067253179478:ℤ)) (.leaf (4769886781051661:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 29 17) 8000 (endpointMeanRuns 29 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 29 17, EndpointRunConditions (endpointMeanCutoff 29 17) (endpointMeanBox 29 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 29 17 h) (endpointMeanCornerA 29 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 17, endpointJoint24Q (endpointMeanCornerK 29 17 h) (endpointMeanCornerA 29 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 29 17, endpointRunWeightQ (endpointMeanCutoff 29 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 29 17) = (414660549/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 29 17 h = (logRoundedQ ((endpointMeanCutoff 29 17:ℚ)/200)).2+(414660549/1000000000000000:ℚ)+((endpointMeanRuns 29 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 29 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 29 17) r*endpointJoint24Q (endpointMeanCornerK 29 17 h) (endpointMeanCornerA 29 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 29 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 29 17 h≤endpointMeanCorner 29 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 29 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint29_17

namespace EndpointAnalyticJoint29_18
private noncomputable def weights : IntegerLookupTree := (.branch 1281 (.branch 799 (.leaf (29928531600000:ℤ)) (.branch 1061 (.leaf (36063384700000:ℤ)) (.leaf (17875258100000:ℤ)))) (.branch 2184 (.branch 1650 (.leaf (17784705300000:ℤ)) (.leaf (10244571000000:ℤ))) (.branch 2856 (.leaf (3364151300000:ℤ)) (.leaf (2012147600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 145 (.branch 126 (.leaf (1933730511826448:ℤ)) (.branch 134 (.leaf (2211786688963560:ℤ)) (.leaf (2367404015736973:ℤ)))) (.branch 170 (.branch 158 (.leaf (2614866213271942:ℤ)) (.leaf (2971933103403924:ℤ))) (.branch 193 (.leaf (3386632219115844:ℤ)) (.leaf (4557435155126125:ℤ))))), (.branch 145 (.branch 126 (.leaf (1946065099766937:ℤ)) (.branch 134 (.leaf (2232005885319752:ℤ)) (.leaf (2392764100720282:ℤ)))) (.branch 170 (.branch 158 (.leaf (2649407091121026:ℤ)) (.leaf (3021748208401427:ℤ))) (.branch 193 (.leaf (3456935231670441:ℤ)) (.leaf (4699298924530971:ℤ))))), (.branch 145 (.branch 126 (.leaf (1942261199062708:ℤ)) (.branch 134 (.leaf (2227579975211554:ℤ)) (.leaf (2388462224160947:ℤ)))) (.branch 170 (.branch 158 (.leaf (2646220774542435:ℤ)) (.leaf (3022636623058199:ℤ))) (.branch 193 (.leaf (3467067253179478:ℤ)) (.leaf (4769886781051661:ℤ))))), (.branch 145 (.branch 126 (.leaf (1955128260289243:ℤ)) (.branch 134 (.leaf (2248832301942041:ℤ)) (.leaf (2415235856959963:ℤ)))) (.branch 170 (.branch 158 (.leaf (2682951885413357:ℤ)) (.leaf (3076191342673125:ℤ))) (.branch 193 (.leaf (3543658146128782:ℤ)) (.leaf (4930829138455675:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 29 18) 8000 (endpointMeanRuns 29 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 29 18, EndpointRunConditions (endpointMeanCutoff 29 18) (endpointMeanBox 29 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 29 18 h) (endpointMeanCornerA 29 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 18, endpointJoint24Q (endpointMeanCornerK 29 18 h) (endpointMeanCornerA 29 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 29 18, endpointRunWeightQ (endpointMeanCutoff 29 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 29 18) = (413378409/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 29 18 h = (logRoundedQ ((endpointMeanCutoff 29 18:ℚ)/200)).2+(413378409/1000000000000000:ℚ)+((endpointMeanRuns 29 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 29 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 29 18) r*endpointJoint24Q (endpointMeanCornerK 29 18 h) (endpointMeanCornerA 29 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 29 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 29 18 h≤endpointMeanCorner 29 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 29 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint29_18

namespace EndpointAnalyticJoint29_19
private noncomputable def weights : IntegerLookupTree := (.branch 1281 (.branch 854 (.leaf (38150766500000:ℤ)) (.branch 1061 (.leaf (25385718800000:ℤ)) (.leaf (17734808800000:ℤ)))) (.branch 2184 (.branch 1650 (.leaf (17661123400000:ℤ)) (.leaf (10182193800000:ℤ))) (.branch 2856 (.leaf (3346030700000:ℤ)) (.leaf (2002498500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 145 (.branch 126 (.leaf (1946065099766937:ℤ)) (.branch 134 (.leaf (2232005885319752:ℤ)) (.leaf (2392764100720282:ℤ)))) (.branch 170 (.branch 158 (.leaf (2649407091121026:ℤ)) (.leaf (3021748208401427:ℤ))) (.branch 187 (.leaf (3456935231670441:ℤ)) (.leaf (4304369558339019:ℤ))))), (.branch 145 (.branch 126 (.leaf (1958478365712837:ℤ)) (.branch 134 (.leaf (2252409916815481:ℤ)) (.leaf (2418395847788337:ℤ)))) (.branch 170 (.branch 158 (.leaf (2684404234088582:ℤ)) (.leaf (3072398306852541:ℤ))) (.branch 187 (.leaf (3528697662683988:ℤ)) (.leaf (4424878517078736:ℤ))))), (.branch 145 (.branch 126 (.leaf (1955128260289243:ℤ)) (.branch 134 (.leaf (2248832301942041:ℤ)) (.leaf (2415235856959963:ℤ)))) (.branch 170 (.branch 158 (.leaf (2682951885413357:ℤ)) (.leaf (3076191342673125:ℤ))) (.branch 187 (.leaf (3543658146128782:ℤ)) (.leaf (4480836780367819:ℤ))))), (.branch 145 (.branch 126 (.leaf (1968080563019179:ℤ)) (.branch 134 (.leaf (2270287387449529:ℤ)) (.leaf (2442309610650993:ℤ)))) (.branch 170 (.branch 158 (.leaf (2720192845847396:ℤ)) (.leaf (3130694938501338:ℤ))) (.branch 187 (.leaf (3621941006511777:ℤ)) (.leaf (4616037450838733:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 29 19) 8000 (endpointMeanRuns 29 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 29 19, EndpointRunConditions (endpointMeanCutoff 29 19) (endpointMeanBox 29 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 29 19 h) (endpointMeanCornerA 29 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 19, endpointJoint24Q (endpointMeanCornerK 29 19 h) (endpointMeanCornerA 29 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 29 19, endpointRunWeightQ (endpointMeanCutoff 29 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 29 19) = (411930383/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 29 19 h = (logRoundedQ ((endpointMeanCutoff 29 19:ℚ)/200)).2+(411930383/1000000000000000:ℚ)+((endpointMeanRuns 29 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 29 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 29 19) r*endpointJoint24Q (endpointMeanCornerK 29 19 h) (endpointMeanCornerA 29 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 29 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 29 19 h≤endpointMeanCorner 29 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 29 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint29_19

namespace EndpointAnalyticJoint29_20
private noncomputable def weights : IntegerLookupTree := (.branch 1281 (.branch 929 (.leaf (50057927900000:ℤ)) (.branch 1061 (.leaf (13919328800000:ℤ)) (.leaf (17613348500000:ℤ)))) (.branch 2184 (.branch 1650 (.leaf (17554249900000:ℤ)) (.leaf (10128250100000:ℤ))) (.branch 2856 (.leaf (3330360100000:ℤ)) (.leaf (1994154000000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 145 (.branch 126 (.leaf (1958478365712837:ℤ)) (.branch 134 (.leaf (2252409916815481:ℤ)) (.leaf (2418395847788337:ℤ)))) (.branch 170 (.branch 158 (.leaf (2684404234088582:ℤ)) (.leaf (3072398306852541:ℤ))) (.branch 180 (.leaf (3528697662683988:ℤ)) (.leaf (4011093196306899:ℤ))))), (.branch 145 (.branch 126 (.leaf (1970970811523507:ℤ)) (.branch 134 (.leaf (2273000473133575:ℤ)) (.leaf (2444302167037401:ℤ)))) (.branch 170 (.branch 158 (.leaf (2719863669174246:ℤ)) (.leaf (3123897394794561:ℤ))) (.branch 180 (.leaf (3601949808187346:ℤ)) (.leaf (4110386293521565:ℤ))))), (.branch 145 (.branch 126 (.leaf (1968080563019179:ℤ)) (.branch 134 (.leaf (2270287387449529:ℤ)) (.leaf (2442309610650993:ℤ)))) (.branch 170 (.branch 158 (.leaf (2720192845847396:ℤ)) (.leaf (3130694938501338:ℤ))) (.branch 180 (.leaf (3621941006511777:ℤ)) (.leaf (4152002561080244:ℤ))))), (.branch 145 (.branch 126 (.leaf (1981118671959076:ℤ)) (.branch 134 (.leaf (2291947166163240:ℤ)) (.leaf (2469686849459969:ℤ)))) (.branch 170 (.branch 158 (.leaf (2757950732858312:ℤ)) (.leaf (3186164222619812:ℤ))) (.branch 180 (.leaf (3701953211537234:ℤ)) (.leaf (4262135393753063:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 29 20) 8000 (endpointMeanRuns 29 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 29 20, EndpointRunConditions (endpointMeanCutoff 29 20) (endpointMeanBox 29 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 29 20 h) (endpointMeanCornerA 29 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 20, endpointJoint24Q (endpointMeanCornerK 29 20 h) (endpointMeanCornerA 29 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 29 20, endpointRunWeightQ (endpointMeanCutoff 29 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 29 20) = (410678131/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 29 20 h = (logRoundedQ ((endpointMeanCutoff 29 20:ℚ)/200)).2+(410678131/1000000000000000:ℚ)+((endpointMeanRuns 29 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 29 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 29 20) r*endpointJoint24Q (endpointMeanCornerK 29 20 h) (endpointMeanCornerA 29 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 29 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 29 20 h≤endpointMeanCorner 29 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 29 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint29_20

namespace EndpointAnalyticJoint29_21
private noncomputable def weights : IntegerLookupTree := (.branch 1650 (.branch 929 (.leaf (47726728200000:ℤ)) (.branch 1281 (.leaf (36078815700000:ℤ)) (.leaf (17448526400000:ℤ)))) (.branch 2184 (.leaf (10074886800000:ℤ)) (.branch 2856 (.leaf (3314858100000:ℤ)) (.leaf (1985899300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 145 (.branch 126 (.leaf (1970970811523507:ℤ)) (.branch 134 (.leaf (2273000473133575:ℤ)) (.leaf (2444302167037401:ℤ)))) (.branch 158 (.leaf (2719863669174246:ℤ)) (.branch 180 (.leaf (3123897394794561:ℤ)) (.leaf (4110386293521565:ℤ))))), (.branch 145 (.branch 126 (.leaf (1983542942259509:ℤ)) (.branch 134 (.leaf (2293779259403209:ℤ)) (.leaf (2470485999737224:ℤ)))) (.branch 158 (.leaf (2755791502990858:ℤ)) (.branch 180 (.leaf (3176259702864317:ℤ)) (.leaf (4212137353857996:ℤ))))), (.branch 145 (.branch 126 (.leaf (1981118671959076:ℤ)) (.branch 134 (.leaf (2291947166163240:ℤ)) (.leaf (2469686849459969:ℤ)))) (.branch 158 (.leaf (2757950732858312:ℤ)) (.branch 180 (.leaf (3186164222619812:ℤ)) (.leaf (4262135393753063:ℤ))))), (.branch 145 (.branch 126 (.leaf (1994243155556560:ℤ)) (.branch 134 (.leaf (2313813590967887:ℤ)) (.leaf (2497370975324353:ℤ)))) (.branch 158 (.leaf (2796232721693003:ℤ)) (.branch 180 (.leaf (3242616304979902:ℤ)) (.leaf (4375189525402491:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 29 21) 8000 (endpointMeanRuns 29 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 29 21, EndpointRunConditions (endpointMeanCutoff 29 21) (endpointMeanBox 29 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 29 21 h) (endpointMeanCornerA 29 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 21, endpointJoint24Q (endpointMeanCornerK 29 21 h) (endpointMeanCornerA 29 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 29 21, endpointRunWeightQ (endpointMeanCutoff 29 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 29 21) = (204719677/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 29 21 h = (logRoundedQ ((endpointMeanCutoff 29 21:ℚ)/200)).2+(204719677/500000000000000:ℚ)+((endpointMeanRuns 29 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 29 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 29 21) r*endpointJoint24Q (endpointMeanCornerK 29 21 h) (endpointMeanCornerA 29 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 29 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 29 21 h≤endpointMeanCorner 29 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 29 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint29_21

namespace EndpointAnalyticJoint29_22
private noncomputable def weights : IntegerLookupTree := (.branch 1281 (.branch 929 (.leaf (45163541100000:ℤ)) (.leaf (35783050900000:ℤ))) (.branch 1650 (.leaf (17329076600000:ℤ)) (.branch 2856 (.leaf (17789489500000:ℤ)) (.leaf (1976572900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 145 (.branch 126 (.leaf (1983542942259509:ℤ)) (.leaf (2293779259403209:ℤ))) (.branch 158 (.leaf (2755791502990858:ℤ)) (.branch 180 (.leaf (3176259702864317:ℤ)) (.leaf (4212137353857996:ℤ))))), (.branch 145 (.branch 126 (.leaf (1996195266203002:ℤ)) (.leaf (2314747996341107:ℤ))) (.branch 158 (.leaf (2792193922816093:ℤ)) (.branch 180 (.leaf (3229499700230435:ℤ)) (.leaf (4316407223264973:ℤ))))), (.branch 145 (.branch 126 (.leaf (1994243155556560:ℤ)) (.leaf (2313813590967887:ℤ))) (.branch 158 (.leaf (2796232721693003:ℤ)) (.branch 180 (.leaf (3242616304979902:ℤ)) (.leaf (4375189525402491:ℤ))))), (.branch 145 (.branch 126 (.leaf (2007454586025094:ℤ)) (.leaf (2335888633379785:ℤ))) (.branch 158 (.leaf (2835046087195042:ℤ)) (.branch 180 (.leaf (3300068598685084:ℤ)) (.leaf (4491242444162660:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 29 22) 8000 (endpointMeanRuns 29 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 29 22, EndpointRunConditions (endpointMeanCutoff 29 22) (endpointMeanBox 29 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 29 22 h) (endpointMeanCornerA 29 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 22, endpointJoint24Q (endpointMeanCornerK 29 22 h) (endpointMeanCornerA 29 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 29 22, endpointRunWeightQ (endpointMeanCutoff 29 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 29 22) = (408039743/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 29 22 h = (logRoundedQ ((endpointMeanCutoff 29 22:ℚ)/200)).2+(408039743/1000000000000000:ℚ)+((endpointMeanRuns 29 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 29 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 29 22) r*endpointJoint24Q (endpointMeanCornerK 29 22 h) (endpointMeanCornerA 29 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 29 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 29 22 h≤endpointMeanCorner 29 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 29 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint29_22

namespace EndpointAnalyticJoint29_23
private noncomputable def weights : IntegerLookupTree := (.branch 1281 (.branch 929 (.leaf (43005889900000:ℤ)) (.leaf (35527174000000:ℤ))) (.branch 1768 (.leaf (21849600000000:ℤ)) (.branch 2856 (.leaf (12409225500000:ℤ)) (.leaf (1968504200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 126 (.leaf (1996195266203002:ℤ)) (.leaf (2314747996341107:ℤ))) (.branch 158 (.leaf (2705819922075008:ℤ)) (.branch 180 (.leaf (3229499700230435:ℤ)) (.leaf (4316407223264973:ℤ))))), (.branch 142 (.branch 126 (.leaf (2008928294878293:ℤ)) (.leaf (2335908420394045:ℤ))) (.branch 158 (.leaf (2739605390764451:ℤ)) (.branch 180 (.leaf (3283632098591669:ℤ)) (.leaf (4423258253909770:ℤ))))), (.branch 142 (.branch 126 (.leaf (2007454586025094:ℤ)) (.leaf (2335888633379785:ℤ))) (.branch 158 (.leaf (2744101408935250:ℤ)) (.branch 180 (.leaf (3300068598685084:ℤ)) (.leaf (4491242444162660:ℤ))))), (.branch 142 (.branch 126 (.leaf (2020753539368926:ℤ)) (.leaf (2358174283724568:ℤ))) (.branch 158 (.leaf (2780062446970742:ℤ)) (.branch 180 (.leaf (3358538825362144:ℤ)) (.leaf (4610373693558455:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 29 23) 8000 (endpointMeanRuns 29 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 29 23, EndpointRunConditions (endpointMeanCutoff 29 23) (endpointMeanBox 29 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 29 23 h) (endpointMeanCornerA 29 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 23, endpointJoint24Q (endpointMeanCornerK 29 23 h) (endpointMeanCornerA 29 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 29 23, endpointRunWeightQ (endpointMeanCutoff 29 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 29 23) = (50853611/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 29 23 h = (logRoundedQ ((endpointMeanCutoff 29 23:ℚ)/200)).2+(50853611/125000000000000:ℚ)+((endpointMeanRuns 29 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 29 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 29 23) r*endpointJoint24Q (endpointMeanCornerK 29 23 h) (endpointMeanCornerA 29 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 29 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 29 23 h≤endpointMeanCorner 29 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 29 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint29_23

namespace EndpointAnalyticJoint29_24
private noncomputable def weights : IntegerLookupTree := (.branch 1281 (.branch 929 (.leaf (40633548300000:ℤ)) (.leaf (35238001400000:ℤ))) (.branch 1768 (.leaf (21703203900000:ℤ)) (.branch 2856 (.leaf (12339386900000:ℤ)) (.leaf (1959385700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 126 (.leaf (2008928294878293:ℤ)) (.leaf (2335908420394045:ℤ))) (.branch 158 (.leaf (2739605390764451:ℤ)) (.branch 180 (.leaf (3283632098591669:ℤ)) (.leaf (4423258253909770:ℤ))))), (.branch 142 (.branch 126 (.leaf (2021742543072531:ℤ)) (.leaf (2357262283882642:ℤ))) (.branch 158 (.leaf (2773812712321940:ℤ)) (.branch 180 (.leaf (3338671856242057:ℤ)) (.leaf (4532754341464005:ℤ))))), (.branch 142 (.branch 126 (.leaf (2020753539368926:ℤ)) (.leaf (2358174283724568:ℤ))) (.branch 158 (.leaf (2780062446970742:ℤ)) (.branch 180 (.leaf (3358538825362144:ℤ)) (.leaf (4610373693558455:ℤ))))), (.branch 142 (.branch 126 (.leaf (2034140595408219:ℤ)) (.leaf (2380672551316679:ℤ))) (.branch 158 (.leaf (2816494749024527:ℤ)) (.branch 180 (.leaf (3418045020627565:ℤ)) (.leaf (4732664927025265:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 29 24) 8000 (endpointMeanRuns 29 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 29 24, EndpointRunConditions (endpointMeanCutoff 29 24) (endpointMeanBox 29 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 29 24 h) (endpointMeanCornerA 29 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 24, endpointJoint24Q (endpointMeanCornerK 29 24 h) (endpointMeanCornerA 29 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 29 24, endpointRunWeightQ (endpointMeanCutoff 29 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 29 24) = (405460473/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 29 24 h = (logRoundedQ ((endpointMeanCutoff 29 24:ℚ)/200)).2+(405460473/1000000000000000:ℚ)+((endpointMeanRuns 29 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 29 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 29 24) r*endpointJoint24Q (endpointMeanCornerK 29 24 h) (endpointMeanCornerA 29 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 29 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 29 24 h≤endpointMeanCorner 29 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 29 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint29_24

namespace EndpointAnalyticJoint29_25
private noncomputable def weights : IntegerLookupTree := (.branch 1768 (.branch 1161 (.leaf (76387247200000:ℤ)) (.leaf (34099977900000:ℤ))) (.branch 2856 (.leaf (12278951800000:ℤ)) (.leaf (1951494900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 126 (.leaf (2021742543072531:ℤ)) (.leaf (2357262283882642:ℤ))) (.branch 164 (.leaf (2773812712321940:ℤ)) (.leaf (3604869654625012:ℤ)))), (.branch 142 (.branch 126 (.leaf (2034638528856512:ℤ)) (.leaf (2378811355146469:ℤ))) (.branch 164 (.leaf (2808447154096123:ℤ)) (.leaf (3672148957790468:ℤ)))), (.branch 142 (.branch 126 (.leaf (2034140595408219:ℤ)) (.leaf (2380672551316679:ℤ))) (.branch 164 (.leaf (2816494749024527:ℤ)) (.leaf (3705943011230252:ℤ)))), (.branch 142 (.branch 126 (.leaf (2047616337804312:ℤ)) (.leaf (2403385464640506:ℤ))) (.branch 164 (.leaf (2853404490941001:ℤ)) (.leaf (3779286594945452:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 29 25) 8000 (endpointMeanRuns 29 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 29 25, EndpointRunConditions (endpointMeanCutoff 29 25) (endpointMeanBox 29 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 29 25 h) (endpointMeanCornerA 29 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 29 25, endpointJoint24Q (endpointMeanCornerK 29 25 h) (endpointMeanCornerA 29 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 29 25, endpointRunWeightQ (endpointMeanCutoff 29 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 29 25) = (404276309/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 29 25 h = (logRoundedQ ((endpointMeanCutoff 29 25:ℚ)/200)).2+(404276309/1000000000000000:ℚ)+((endpointMeanRuns 29 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 29 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 29 25) r*endpointJoint24Q (endpointMeanCornerK 29 25 h) (endpointMeanCornerA 29 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 29 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 29 25 h≤endpointMeanCorner 29 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 29 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint29_25

private theorem activeIndices24 : ∀ai : Fin 42, endpointMeanActive 24 ai → ai∈
    ([6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow24 (ai : Fin 42) : endpointMeanActive 24 ai →
    EndpointJointNumericalConditions 24 ai := by
  intro hact
  have hi := activeIndices24 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint24_06.conditions
  · exact EndpointAnalyticJoint24_07.conditions
  · exact EndpointAnalyticJoint24_08.conditions
  · exact EndpointAnalyticJoint24_09.conditions
  · exact EndpointAnalyticJoint24_10.conditions
  · exact EndpointAnalyticJoint24_11.conditions
  · exact EndpointAnalyticJoint24_12.conditions
  · exact EndpointAnalyticJoint24_13.conditions
  · exact EndpointAnalyticJoint24_14.conditions
  · exact EndpointAnalyticJoint24_15.conditions
  · exact EndpointAnalyticJoint24_16.conditions
  · exact EndpointAnalyticJoint24_17.conditions
  · exact EndpointAnalyticJoint24_18.conditions
  · exact EndpointAnalyticJoint24_19.conditions
  · exact EndpointAnalyticJoint24_20.conditions
  · exact EndpointAnalyticJoint24_21.conditions
  · exact EndpointAnalyticJoint24_22.conditions

private theorem activeIndices25 : ∀ai : Fin 42, endpointMeanActive 25 ai → ai∈
    ([7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow25 (ai : Fin 42) : endpointMeanActive 25 ai →
    EndpointJointNumericalConditions 25 ai := by
  intro hact
  have hi := activeIndices25 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint25_07.conditions
  · exact EndpointAnalyticJoint25_08.conditions
  · exact EndpointAnalyticJoint25_09.conditions
  · exact EndpointAnalyticJoint25_10.conditions
  · exact EndpointAnalyticJoint25_11.conditions
  · exact EndpointAnalyticJoint25_12.conditions
  · exact EndpointAnalyticJoint25_13.conditions
  · exact EndpointAnalyticJoint25_14.conditions
  · exact EndpointAnalyticJoint25_15.conditions
  · exact EndpointAnalyticJoint25_16.conditions
  · exact EndpointAnalyticJoint25_17.conditions
  · exact EndpointAnalyticJoint25_18.conditions
  · exact EndpointAnalyticJoint25_19.conditions
  · exact EndpointAnalyticJoint25_20.conditions
  · exact EndpointAnalyticJoint25_21.conditions
  · exact EndpointAnalyticJoint25_22.conditions
  · exact EndpointAnalyticJoint25_23.conditions

private theorem activeIndices26 : ∀ai : Fin 42, endpointMeanActive 26 ai → ai∈
    ([7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow26 (ai : Fin 42) : endpointMeanActive 26 ai →
    EndpointJointNumericalConditions 26 ai := by
  intro hact
  have hi := activeIndices26 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint26_07.conditions
  · exact EndpointAnalyticJoint26_08.conditions
  · exact EndpointAnalyticJoint26_09.conditions
  · exact EndpointAnalyticJoint26_10.conditions
  · exact EndpointAnalyticJoint26_11.conditions
  · exact EndpointAnalyticJoint26_12.conditions
  · exact EndpointAnalyticJoint26_13.conditions
  · exact EndpointAnalyticJoint26_14.conditions
  · exact EndpointAnalyticJoint26_15.conditions
  · exact EndpointAnalyticJoint26_16.conditions
  · exact EndpointAnalyticJoint26_17.conditions
  · exact EndpointAnalyticJoint26_18.conditions
  · exact EndpointAnalyticJoint26_19.conditions
  · exact EndpointAnalyticJoint26_20.conditions
  · exact EndpointAnalyticJoint26_21.conditions
  · exact EndpointAnalyticJoint26_22.conditions
  · exact EndpointAnalyticJoint26_23.conditions

private theorem activeIndices27 : ∀ai : Fin 42, endpointMeanActive 27 ai → ai∈
    ([8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow27 (ai : Fin 42) : endpointMeanActive 27 ai →
    EndpointJointNumericalConditions 27 ai := by
  intro hact
  have hi := activeIndices27 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint27_08.conditions
  · exact EndpointAnalyticJoint27_09.conditions
  · exact EndpointAnalyticJoint27_10.conditions
  · exact EndpointAnalyticJoint27_11.conditions
  · exact EndpointAnalyticJoint27_12.conditions
  · exact EndpointAnalyticJoint27_13.conditions
  · exact EndpointAnalyticJoint27_14.conditions
  · exact EndpointAnalyticJoint27_15.conditions
  · exact EndpointAnalyticJoint27_16.conditions
  · exact EndpointAnalyticJoint27_17.conditions
  · exact EndpointAnalyticJoint27_18.conditions
  · exact EndpointAnalyticJoint27_19.conditions
  · exact EndpointAnalyticJoint27_20.conditions
  · exact EndpointAnalyticJoint27_21.conditions
  · exact EndpointAnalyticJoint27_22.conditions
  · exact EndpointAnalyticJoint27_23.conditions
  · exact EndpointAnalyticJoint27_24.conditions

private theorem activeIndices28 : ∀ai : Fin 42, endpointMeanActive 28 ai → ai∈
    ([8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow28 (ai : Fin 42) : endpointMeanActive 28 ai →
    EndpointJointNumericalConditions 28 ai := by
  intro hact
  have hi := activeIndices28 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint28_08.conditions
  · exact EndpointAnalyticJoint28_09.conditions
  · exact EndpointAnalyticJoint28_10.conditions
  · exact EndpointAnalyticJoint28_11.conditions
  · exact EndpointAnalyticJoint28_12.conditions
  · exact EndpointAnalyticJoint28_13.conditions
  · exact EndpointAnalyticJoint28_14.conditions
  · exact EndpointAnalyticJoint28_15.conditions
  · exact EndpointAnalyticJoint28_16.conditions
  · exact EndpointAnalyticJoint28_17.conditions
  · exact EndpointAnalyticJoint28_18.conditions
  · exact EndpointAnalyticJoint28_19.conditions
  · exact EndpointAnalyticJoint28_20.conditions
  · exact EndpointAnalyticJoint28_21.conditions
  · exact EndpointAnalyticJoint28_22.conditions
  · exact EndpointAnalyticJoint28_23.conditions
  · exact EndpointAnalyticJoint28_24.conditions

private theorem activeIndices29 : ∀ai : Fin 42, endpointMeanActive 29 ai → ai∈
    ([9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow29 (ai : Fin 42) : endpointMeanActive 29 ai →
    EndpointJointNumericalConditions 29 ai := by
  intro hact
  have hi := activeIndices29 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint29_09.conditions
  · exact EndpointAnalyticJoint29_10.conditions
  · exact EndpointAnalyticJoint29_11.conditions
  · exact EndpointAnalyticJoint29_12.conditions
  · exact EndpointAnalyticJoint29_13.conditions
  · exact EndpointAnalyticJoint29_14.conditions
  · exact EndpointAnalyticJoint29_15.conditions
  · exact EndpointAnalyticJoint29_16.conditions
  · exact EndpointAnalyticJoint29_17.conditions
  · exact EndpointAnalyticJoint29_18.conditions
  · exact EndpointAnalyticJoint29_19.conditions
  · exact EndpointAnalyticJoint29_20.conditions
  · exact EndpointAnalyticJoint29_21.conditions
  · exact EndpointAnalyticJoint29_22.conditions
  · exact EndpointAnalyticJoint29_23.conditions
  · exact EndpointAnalyticJoint29_24.conditions
  · exact EndpointAnalyticJoint29_25.conditions

end SingularValueBounds.KL.Certificates
