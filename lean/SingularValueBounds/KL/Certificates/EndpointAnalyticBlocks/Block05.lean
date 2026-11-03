import SingularValueBounds.KL.Certificates.EndpointAnalyticLogs
import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SingularValueBounds.KL.Certificates

namespace EndpointAnalyticJoint30_09
private noncomputable def weights : IntegerLookupTree := (.branch 971 (.leaf (88898391300000:ℤ)) (.branch 1693 (.leaf (68816166400000:ℤ)) (.leaf (41087979500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 143 (.leaf (1839477941377559:ℤ)) (.branch 175 (.leaf (2327042011021436:ℤ)) (.leaf (3030014090691145:ℤ)))), (.branch 143 (.leaf (1842326853784379:ℤ)) (.branch 175 (.leaf (2334291195233047:ℤ)) (.leaf (3047046876559421:ℤ)))), (.branch 143 (.leaf (1844093786750421:ℤ)) (.branch 175 (.leaf (2342494229282124:ℤ)) (.leaf (3080570701710859:ℤ)))), (.branch 143 (.leaf (1847060942293307:ℤ)) (.branch 175 (.leaf (2350164820688844:ℤ)) (.leaf (3099118231338348:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 30 9) 8000 (endpointMeanRuns 30 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 30 9, EndpointRunConditions (endpointMeanCutoff 30 9) (endpointMeanBox 30 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 30 9 h) (endpointMeanCornerA 30 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 9, endpointJoint24Q (endpointMeanCornerK 30 9 h) (endpointMeanCornerA 30 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 30 9, endpointRunWeightQ (endpointMeanCutoff 30 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 30 9) = (105766041/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 30 9 h = (logRoundedQ ((endpointMeanCutoff 30 9:ℚ)/200)).2+(105766041/250000000000000:ℚ)+((endpointMeanRuns 30 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 30 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 30 9) r*endpointJoint24Q (endpointMeanCornerK 30 9 h) (endpointMeanCornerA 30 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 30 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 30 9 h≤endpointMeanCorner 30 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 30 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint30_09

namespace EndpointAnalyticJoint30_10
private noncomputable def weights : IntegerLookupTree := (.branch 1255 (.branch 828 (.leaf (52810137000000:ℤ)) (.leaf (59428781500000:ℤ))) (.branch 2800 (.leaf (59555803700000:ℤ)) (.leaf (2395550800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 158 (.branch 126 (.leaf (1842326853784379:ℤ)) (.leaf (2064634499529079:ℤ))) (.branch 188 (.leaf (2626435234151311:ℤ)) (.leaf (3465104900587335:ℤ)))), (.branch 158 (.branch 126 (.leaf (1854531871543252:ℤ)) (.leaf (2084332237635584:ℤ))) (.branch 188 (.leaf (2672970104230873:ℤ)) (.leaf (3571612581036025:ℤ)))), (.branch 158 (.branch 126 (.leaf (1847060942293307:ℤ)) (.leaf (2073327419074934:ℤ))) (.branch 188 (.leaf (2653722319543130:ℤ)) (.leaf (3554130199095232:ℤ)))), (.branch 158 (.branch 126 (.leaf (1859774540428635:ℤ)) (.leaf (2093987707520306:ℤ))) (.branch 188 (.leaf (2703533533812588:ℤ)) (.leaf (3672679115414031:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 30 10) 8000 (endpointMeanRuns 30 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 30 10, EndpointRunConditions (endpointMeanCutoff 30 10) (endpointMeanBox 30 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 30 10 h) (endpointMeanCornerA 30 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 10, endpointJoint24Q (endpointMeanCornerK 30 10 h) (endpointMeanCornerA 30 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 30 10, endpointRunWeightQ (endpointMeanCutoff 30 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 30 10) = (211038863/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 30 10 h = (logRoundedQ ((endpointMeanCutoff 30 10:ℚ)/200)).2+(211038863/500000000000000:ℚ)+((endpointMeanRuns 30 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 30 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 30 10) r*endpointJoint24Q (endpointMeanCornerK 30 10 h) (endpointMeanCornerA 30 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 30 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 30 10 h≤endpointMeanCorner 30 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 30 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint30_10

namespace EndpointAnalyticJoint30_11
private noncomputable def weights : IntegerLookupTree := (.branch 1255 (.branch 828 (.leaf (50085511800000:ℤ)) (.leaf (58961705200000:ℤ))) (.branch 2800 (.leaf (59195709700000:ℤ)) (.leaf (2384940200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 158 (.branch 126 (.leaf (1854531871543252:ℤ)) (.leaf (2084332237635584:ℤ))) (.branch 188 (.leaf (2672970104230873:ℤ)) (.leaf (3571612581036025:ℤ)))), (.branch 158 (.branch 126 (.leaf (1866817744910449:ℤ)) (.leaf (2104217902896564:ℤ))) (.branch 188 (.leaf (2720329473656606:ℤ)) (.leaf (3681394011145978:ℤ)))), (.branch 158 (.branch 126 (.leaf (1859774540428635:ℤ)) (.leaf (2093987707520306:ℤ))) (.branch 188 (.leaf (2703533533812588:ℤ)) (.leaf (3672679115414031:ℤ)))), (.branch 158 (.branch 126 (.leaf (1872575648171171:ℤ)) (.leaf (2114853871561945:ℤ))) (.branch 188 (.leaf (2754279720459791:ℤ)) (.leaf (3795182260974053:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 30 11) 8000 (endpointMeanRuns 30 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 30 11, EndpointRunConditions (endpointMeanCutoff 30 11) (endpointMeanBox 30 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 30 11 h) (endpointMeanCornerA 30 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 11, endpointJoint24Q (endpointMeanCornerK 30 11 h) (endpointMeanCornerA 30 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 30 11, endpointRunWeightQ (endpointMeanCutoff 30 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 30 11) = (420710761/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 30 11 h = (logRoundedQ ((endpointMeanCutoff 30 11:ℚ)/200)).2+(420710761/1000000000000000:ℚ)+((endpointMeanRuns 30 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 30 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 30 11) r*endpointJoint24Q (endpointMeanCornerK 30 11 h) (endpointMeanCornerA 30 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 30 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 30 11 h≤endpointMeanCorner 30 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 30 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint30_11

namespace EndpointAnalyticJoint30_12
private noncomputable def weights : IntegerLookupTree := (.branch 1255 (.branch 828 (.leaf (47097000300000:ℤ)) (.leaf (58434608000000:ℤ))) (.branch 1693 (.leaf (23190098200000:ℤ)) (.branch 2800 (.leaf (16269199200000:ℤ)) (.leaf (2372966100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 143 (.branch 126 (.leaf (1866817744910449:ℤ)) (.leaf (2104217902896564:ℤ))) (.branch 158 (.leaf (2397076682740683:ℤ)) (.branch 188 (.leaf (2720329473656606:ℤ)) (.leaf (3681394011145978:ℤ))))), (.branch 143 (.branch 126 (.leaf (1879185009536926:ℤ)) (.leaf (2124293288239458:ℤ))) (.branch 158 (.leaf (2429099894413459:ℤ)) (.branch 188 (.leaf (2768527950810798:ℤ)) (.leaf (3794549816870179:ℤ))))), (.branch 143 (.branch 126 (.leaf (1872575648171171:ℤ)) (.leaf (2114853871561945:ℤ))) (.branch 158 (.leaf (2416650654837278:ℤ)) (.branch 188 (.leaf (2754279720459791:ℤ)) (.leaf (3795182260974053:ℤ))))), (.branch 143 (.branch 126 (.leaf (1885464867862695:ℤ)) (.leaf (2135927962708525:ℤ))) (.branch 158 (.leaf (2450595609202001:ℤ)) (.branch 188 (.leaf (2805978429214462:ℤ)) (.leaf (3921771530096881:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 30 12) 8000 (endpointMeanRuns 30 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 30 12, EndpointRunConditions (endpointMeanCutoff 30 12) (endpointMeanBox 30 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 30 12 h) (endpointMeanCornerA 30 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 12, endpointJoint24Q (endpointMeanCornerK 30 12 h) (endpointMeanCornerA 30 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 30 12, endpointRunWeightQ (endpointMeanCutoff 30 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 30 12) = (419168137/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 30 12 h = (logRoundedQ ((endpointMeanCutoff 30 12:ℚ)/200)).2+(419168137/1000000000000000:ℚ)+((endpointMeanRuns 30 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 30 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 30 12) r*endpointJoint24Q (endpointMeanCornerK 30 12 h) (endpointMeanCornerA 30 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 30 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 30 12 h≤endpointMeanCorner 30 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 30 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint30_12

namespace EndpointAnalyticJoint30_13
private noncomputable def weights : IntegerLookupTree := (.branch 1324 (.branch 998 (.leaf (81513299100000:ℤ)) (.leaf (31357239200000:ℤ))) (.branch 1693 (.leaf (17000352100000:ℤ)) (.branch 2800 (.leaf (16182867500000:ℤ)) (.leaf (2362618900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 143 (.branch 126 (.leaf (1879185009536926:ℤ)) (.leaf (2124293288239458:ℤ))) (.branch 155 (.leaf (2429099894413459:ℤ)) (.branch 173 (.leaf (2694050682827813:ℤ)) (.leaf (3205569605146276:ℤ))))), (.branch 143 (.branch 126 (.leaf (1891634204622201:ℤ)) (.leaf (2144560203697230:ℤ))) (.branch 155 (.leaf (2461550913045112:ℤ)) (.branch 173 (.leaf (2739196983501151:ℤ)) (.leaf (3280376638236480:ℤ))))), (.branch 143 (.branch 126 (.leaf (1885464867862695:ℤ)) (.leaf (2135927962708525:ℤ))) (.branch 155 (.leaf (2450595609202001:ℤ)) (.branch 173 (.leaf (2727505613312345:ℤ)) (.leaf (3272786171487862:ℤ))))), (.branch 143 (.branch 126 (.leaf (1898442805990994:ℤ)) (.leaf (2157212052911599:ℤ))) (.branch 155 (.leaf (2485017363936903:ℤ)) (.branch 173 (.leaf (2775846555576141:ℤ)) (.leaf (3354512336449280:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 30 13) 8000 (endpointMeanRuns 30 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 30 13, EndpointRunConditions (endpointMeanCutoff 30 13) (endpointMeanBox 30 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 30 13 h) (endpointMeanCornerA 30 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 13, endpointJoint24Q (endpointMeanCornerK 30 13 h) (endpointMeanCornerA 30 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 30 13, endpointRunWeightQ (endpointMeanCutoff 30 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 30 13) = (417835093/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 30 13 h = (logRoundedQ ((endpointMeanCutoff 30 13:ℚ)/200)).2+(417835093/1000000000000000:ℚ)+((endpointMeanRuns 30 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 30 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 30 13) r*endpointJoint24Q (endpointMeanCornerK 30 13 h) (endpointMeanCornerA 30 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 30 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 30 13 h≤endpointMeanCorner 30 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 30 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint30_13

namespace EndpointAnalyticJoint30_14
private noncomputable def weights : IntegerLookupTree := (.branch 1324 (.branch 910 (.leaf (59324787600000:ℤ)) (.leaf (46884705000000:ℤ))) (.branch 1693 (.leaf (16882092000000:ℤ)) (.branch 2800 (.leaf (16085411500000:ℤ)) (.leaf (2350938300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 143 (.branch 126 (.leaf (1891634204622201:ℤ)) (.leaf (2144560203697230:ℤ))) (.branch 155 (.leaf (2461550913045112:ℤ)) (.branch 180 (.leaf (2739196983501151:ℤ)) (.leaf (3548459387305103:ℤ))))), (.branch 143 (.branch 126 (.leaf (1904165872937889:ℤ)) (.leaf (2165020476571535:ℤ))) (.branch 155 (.leaf (2494435453827360:ℤ)) (.branch 180 (.leaf (2785099835815289:ℤ)) (.leaf (3642583097057033:ℤ))))), (.branch 143 (.branch 126 (.leaf (1898442805990994:ℤ)) (.leaf (2157212052911599:ℤ))) (.branch 155 (.leaf (2485017363936903:ℤ)) (.branch 180 (.leaf (2775846555576141:ℤ)) (.leaf (3647791327951382:ℤ))))), (.branch 143 (.branch 126 (.leaf (1911510073218417:ℤ)) (.leaf (2178708234769298:ℤ))) (.branch 155 (.leaf (2519922616314003:ℤ)) (.branch 180 (.leaf (2825044268468582:ℤ)) (.leaf (3751941468213669:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 30 14) 8000 (endpointMeanRuns 30 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 30 14, EndpointRunConditions (endpointMeanCutoff 30 14) (endpointMeanBox 30 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 30 14 h) (endpointMeanCornerA 30 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 14, endpointJoint24Q (endpointMeanCornerK 30 14 h) (endpointMeanCornerA 30 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 30 14, endpointRunWeightQ (endpointMeanCutoff 30 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 30 14) = (416330279/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 30 14 h = (logRoundedQ ((endpointMeanCutoff 30 14:ℚ)/200)).2+(416330279/1000000000000000:ℚ)+((endpointMeanRuns 30 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 30 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 30 14) r*endpointJoint24Q (endpointMeanCornerK 30 14 h) (endpointMeanCornerA 30 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 30 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 30 14 h≤endpointMeanCorner 30 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 30 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint30_14

namespace EndpointAnalyticJoint30_15
private noncomputable def weights : IntegerLookupTree := (.branch 1120 (.branch 910 (.leaf (56606534200000:ℤ)) (.leaf (24300676000000:ℤ))) (.branch 1655 (.leaf (36630376100000:ℤ)) (.branch 2800 (.leaf (17944871100000:ℤ)) (.leaf (2340841500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 144 (.branch 126 (.leaf (1904165872937889:ℤ)) (.leaf (2165020476571535:ℤ))) (.branch 165 (.leaf (2516550574536786:ℤ)) (.branch 180 (.leaf (3078234370731818:ℤ)) (.leaf (3642583097057033:ℤ))))), (.branch 144 (.branch 126 (.leaf (1916780560851332:ℤ)) (.leaf (2185675951597483:ℤ))) (.branch 165 (.leaf (2550820538343148:ℤ)) (.branch 180 (.leaf (3140284041103267:ℤ)) (.leaf (3739203460080283:ℤ))))), (.branch 144 (.branch 126 (.leaf (1911510073218417:ℤ)) (.leaf (2178708234769298:ℤ))) (.branch 165 (.leaf (2542997539966096:ℤ)) (.branch 180 (.leaf (3137106139850073:ℤ)) (.leaf (3751941468213669:ℤ))))), (.branch 144 (.branch 126 (.leaf (1924667284410569:ℤ)) (.leaf (2200418621732076:ℤ))) (.branch 165 (.leaf (2579424779351160:ℤ)) (.branch 180 (.leaf (3204387019005474:ℤ)) (.leaf (3859065257662937:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 30 15) 8000 (endpointMeanRuns 30 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 30 15, EndpointRunConditions (endpointMeanCutoff 30 15) (endpointMeanBox 30 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 30 15 h) (endpointMeanCornerA 30 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 15, endpointJoint24Q (endpointMeanCornerK 30 15 h) (endpointMeanCornerA 30 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 30 15, endpointRunWeightQ (endpointMeanCutoff 30 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 30 15) = (415029513/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 30 15 h = (logRoundedQ ((endpointMeanCutoff 30 15:ℚ)/200)).2+(415029513/1000000000000000:ℚ)+((endpointMeanRuns 30 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 30 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 30 15) r*endpointJoint24Q (endpointMeanCornerK 30 15 h) (endpointMeanCornerA 30 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 30 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 30 15 h≤endpointMeanCorner 30 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 30 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint30_15

namespace EndpointAnalyticJoint30_16
private noncomputable def weights : IntegerLookupTree := (.branch 1324 (.branch 847 (.leaf (40831666500000:ℤ)) (.branch 998 (.leaf (19548076000000:ℤ)) (.leaf (30635678700000:ℤ)))) (.branch 1655 (.leaf (15152642200000:ℤ)) (.branch 2800 (.leaf (17837269000000:ℤ)) (.leaf (2329440400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 126 (.leaf (1916780560851332:ℤ)) (.branch 144 (.leaf (2185675951597483:ℤ)) (.leaf (2550820538343148:ℤ)))) (.branch 173 (.leaf (2831771917893936:ℤ)) (.branch 186 (.leaf (3435268665072666:ℤ)) (.leaf (4043222652411089:ℤ))))), (.branch 155 (.branch 126 (.leaf (1929478818349453:ℤ)) (.branch 144 (.leaf (2206528491109962:ℤ)) (.leaf (2585557184771027:ℤ)))) (.branch 173 (.leaf (2879226120317985:ℤ)) (.branch 186 (.leaf (3515436088762131:ℤ)) (.leaf (4162984267147015:ℤ))))), (.branch 155 (.branch 126 (.leaf (1924667284410569:ℤ)) (.branch 144 (.leaf (2200418621732076:ℤ)) (.leaf (2579424779351160:ℤ)))) (.branch 173 (.leaf (2875113936962813:ℤ)) (.branch 186 (.leaf (3524138087248211:ℤ)) (.leaf (4200094455816053:ℤ))))), (.branch 155 (.branch 126 (.leaf (1937915058665289:ℤ)) (.branch 144 (.leaf (2222345348310478:ℤ)) (.leaf (2616373821745607:ℤ)))) (.branch 173 (.leaf (2926071015162831:ℤ)) (.branch 186 (.leaf (3612140870068064:ℤ)) (.leaf (4334803163785387:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 30 16) 8000 (endpointMeanRuns 30 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 30 16, EndpointRunConditions (endpointMeanCutoff 30 16) (endpointMeanBox 30 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 30 16 h) (endpointMeanCornerA 30 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 16, endpointJoint24Q (endpointMeanCornerK 30 16 h) (endpointMeanCornerA 30 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 30 16, endpointRunWeightQ (endpointMeanCutoff 30 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 30 16) = (4135607/10000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 30 16 h = (logRoundedQ ((endpointMeanCutoff 30 16:ℚ)/200)).2+(4135607/10000000000000:ℚ)+((endpointMeanRuns 30 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 30 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 30 16) r*endpointJoint24Q (endpointMeanCornerK 30 16 h) (endpointMeanCornerA 30 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 30 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 30 16 h≤endpointMeanCorner 30 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 30 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint30_16

namespace EndpointAnalyticJoint30_17
private noncomputable def weights : IntegerLookupTree := (.branch 1324 (.branch 828 (.leaf (34562344400000:ℤ)) (.branch 998 (.leaf (22605347300000:ℤ)) (.leaf (30390852300000:ℤ)))) (.branch 1655 (.leaf (15048576800000:ℤ)) (.branch 2800 (.leaf (17731022700000:ℤ)) (.leaf (2318182900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 126 (.leaf (1929478818349453:ℤ)) (.branch 144 (.leaf (2206528491109962:ℤ)) (.leaf (2585557184771027:ℤ)))) (.branch 173 (.leaf (2879226120317985:ℤ)) (.branch 188 (.leaf (3515436088762131:ℤ)) (.leaf (4283039585624209:ℤ))))), (.branch 155 (.branch 126 (.leaf (1942261199062708:ℤ)) (.branch 144 (.leaf (2227579975211554:ℤ)) (.leaf (2620766869026106:ℤ)))) (.branch 173 (.leaf (2927475549685796:ℤ)) (.branch 188 (.leaf (3597474345986789:ℤ)) (.leaf (4414688301787876:ℤ))))), (.branch 155 (.branch 126 (.leaf (1937915058665289:ℤ)) (.branch 144 (.leaf (2222345348310478:ℤ)) (.leaf (2616373821745607:ℤ)))) (.branch 173 (.leaf (2926071015162831:ℤ)) (.branch 188 (.leaf (3612140870068064:ℤ)) (.leaf (4471784822558565:ℤ))))), (.branch 155 (.branch 126 (.leaf (1951254019341746:ℤ)) (.branch 144 (.leaf (2244490570285025:ℤ)) (.leaf (2653852141731242:ℤ)))) (.branch 173 (.leaf (2977931231073431:ℤ)) (.branch 188 (.leaf (3702341208600070:ℤ)) (.leaf (4620942342128375:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 30 17) 8000 (endpointMeanRuns 30 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 30 17, EndpointRunConditions (endpointMeanCutoff 30 17) (endpointMeanBox 30 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 30 17 h) (endpointMeanCornerA 30 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 17, endpointJoint24Q (endpointMeanCornerK 30 17 h) (endpointMeanCornerA 30 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 30 17, endpointRunWeightQ (endpointMeanCutoff 30 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 30 17) = (412110393/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 30 17 h = (logRoundedQ ((endpointMeanCutoff 30 17:ℚ)/200)).2+(412110393/1000000000000000:ℚ)+((endpointMeanRuns 30 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 30 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 30 17) r*endpointJoint24Q (endpointMeanCornerK 30 17 h) (endpointMeanCornerA 30 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 30 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 30 17 h≤endpointMeanCorner 30 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 30 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint30_17

namespace EndpointAnalyticJoint30_18
private noncomputable def weights : IntegerLookupTree := (.branch 1324 (.branch 910 (.leaf (48338752500000:ℤ)) (.branch 1120 (.leaf (23701599000000:ℤ)) (.leaf (14989173800000:ℤ)))) (.branch 1655 (.leaf (14958582800000:ℤ)) (.branch 2800 (.leaf (17639142600000:ℤ)) (.leaf (2308447600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 126 (.leaf (1942261199062708:ℤ)) (.branch 144 (.leaf (2227579975211554:ℤ)) (.leaf (2620766869026106:ℤ)))) (.branch 165 (.leaf (2927475549685796:ℤ)) (.branch 180 (.leaf (3268160902727589:ℤ)) (.leaf (3940200799788437:ℤ))))), (.branch 155 (.branch 126 (.leaf (1955128260289243:ℤ)) (.branch 144 (.leaf (2248832301942041:ℤ)) (.leaf (2656456032858220:ℤ)))) (.branch 165 (.leaf (2976533532233191:ℤ)) (.branch 180 (.leaf (3334039027104092:ℤ)) (.leaf (4044715541529715:ℤ))))), (.branch 155 (.branch 126 (.leaf (1951254019341746:ℤ)) (.branch 144 (.leaf (2244490570285025:ℤ)) (.leaf (2653852141731242:ℤ)))) (.branch 165 (.leaf (2977931231073431:ℤ)) (.branch 180 (.leaf (3343308602283960:ℤ)) (.leaf (4082575817533059:ℤ))))), (.branch 155 (.branch 126 (.leaf (1964684794089794:ℤ)) (.branch 144 (.leaf (2266856464918156:ℤ)) (.leaf (2691867320959723:ℤ)))) (.branch 165 (.leaf (3030710591454675:ℤ)) (.branch 180 (.leaf (3415011863831954:ℤ)) (.leaf (4199139734106181:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 30 18) 8000 (endpointMeanRuns 30 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 30 18, EndpointRunConditions (endpointMeanCutoff 30 18) (endpointMeanBox 30 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 30 18 h) (endpointMeanCornerA 30 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 18, endpointJoint24Q (endpointMeanCornerK 30 18 h) (endpointMeanCornerA 30 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 30 18, endpointRunWeightQ (endpointMeanCutoff 30 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 30 18) = (1604907/3906250000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 30 18 h = (logRoundedQ ((endpointMeanCutoff 30 18:ℚ)/200)).2+(1604907/3906250000000:ℚ)+((endpointMeanRuns 30 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 30 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 30 18) r*endpointJoint24Q (endpointMeanCornerK 30 18 h) (endpointMeanCornerA 30 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 30 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 30 18 h≤endpointMeanCorner 30 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 30 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint30_18

namespace EndpointAnalyticJoint30_19
private noncomputable def weights : IntegerLookupTree := (.branch 1324 (.branch 910 (.leaf (45686350600000:ℤ)) (.branch 1120 (.leaf (23498213000000:ℤ)) (.leaf (14875614800000:ℤ)))) (.branch 1655 (.leaf (14856919000000:ℤ)) (.branch 2800 (.leaf (17535348100000:ℤ)) (.leaf (2297449900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 155 (.branch 126 (.leaf (1955128260289243:ℤ)) (.branch 144 (.leaf (2248832301942041:ℤ)) (.leaf (2656456032858220:ℤ)))) (.branch 165 (.leaf (2976533532233191:ℤ)) (.branch 180 (.leaf (3334039027104092:ℤ)) (.leaf (4044715541529715:ℤ))))), (.branch 155 (.branch 126 (.leaf (1968080563019179:ℤ)) (.branch 144 (.leaf (2270287387449529:ℤ)) (.leaf (2692631205739857:ℤ)))) (.branch 165 (.leaf (3026413617514073:ℤ)) (.branch 180 (.leaf (3401245093219246:ℤ)) (.leaf (4152002561080244:ℤ))))), (.branch 155 (.branch 126 (.leaf (1964684794089794:ℤ)) (.branch 144 (.leaf (2266856464918156:ℤ)) (.leaf (2691867320959723:ℤ)))) (.branch 165 (.leaf (3030710591454675:ℤ)) (.branch 180 (.leaf (3415011863831954:ℤ)) (.leaf (4199139734106181:ℤ))))), (.branch 155 (.branch 126 (.leaf (1978208014879484:ℤ)) (.branch 144 (.leaf (2289445231168287:ℤ)) (.leaf (2730427049686291:ℤ)))) (.branch 165 (.leaf (3084425386762415:ℤ)) (.branch 180 (.leaf (3488252930688468:ℤ)) (.leaf (4319031732570278:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 30 19) 8000 (endpointMeanRuns 30 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 30 19, EndpointRunConditions (endpointMeanCutoff 30 19) (endpointMeanBox 30 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 30 19 h) (endpointMeanCornerA 30 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 19, endpointJoint24Q (endpointMeanCornerK 30 19 h) (endpointMeanCornerA 30 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 30 19, endpointRunWeightQ (endpointMeanCutoff 30 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 30 19) = (204719677/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 30 19 h = (logRoundedQ ((endpointMeanCutoff 30 19:ℚ)/200)).2+(204719677/500000000000000:ℚ)+((endpointMeanRuns 30 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 30 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 30 19) r*endpointJoint24Q (endpointMeanCornerK 30 19 h) (endpointMeanCornerA 30 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 30 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 30 19 h≤endpointMeanCorner 30 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 30 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint30_19

namespace EndpointAnalyticJoint30_20
private noncomputable def weights : IntegerLookupTree := (.branch 1655 (.branch 998 (.leaf (59489747300000:ℤ)) (.branch 1324 (.leaf (29733062500000:ℤ)) (.leaf (14768978100000:ℤ)))) (.branch 2141 (.leaf (9495777800000:ℤ)) (.branch 2800 (.leaf (3725170000000:ℤ)) (.leaf (2287936700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 144 (.branch 126 (.leaf (1968080563019179:ℤ)) (.branch 134 (.leaf (2270287387449529:ℤ)) (.leaf (2442309610650993:ℤ)))) (.branch 155 (.leaf (2692631205739857:ℤ)) (.branch 173 (.leaf (3026413617514073:ℤ)) (.leaf (3767339015319586:ℤ))))), (.branch 144 (.branch 126 (.leaf (1981118671959076:ℤ)) (.branch 134 (.leaf (2291947166163240:ℤ)) (.leaf (2469686849459969:ℤ)))) (.branch 155 (.leaf (2729299006060769:ℤ)) (.branch 173 (.leaf (3077129582142760:ℤ)) (.leaf (3855255825464211:ℤ))))), (.branch 144 (.branch 126 (.leaf (1978208014879484:ℤ)) (.branch 134 (.leaf (2289445231168287:ℤ)) (.leaf (2468169642614294:ℤ)))) (.branch 155 (.leaf (2730427049686291:ℤ)) (.branch 173 (.leaf (3084425386762415:ℤ)) (.leaf (3889555427608525:ℤ))))), (.branch 144 (.branch 126 (.leaf (1991824318030821:ℤ)) (.branch 134 (.leaf (2312259089906013:ℤ)) (.leaf (2497151500804259:ℤ)))) (.branch 155 (.leaf (2769539128325459:ℤ)) (.branch 173 (.leaf (3139092196176374:ℤ)) (.leaf (3986683205546679:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 30 20) 8000 (endpointMeanRuns 30 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 30 20, EndpointRunConditions (endpointMeanCutoff 30 20) (endpointMeanBox 30 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 30 20 h) (endpointMeanCornerA 30 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 20, endpointJoint24Q (endpointMeanCornerK 30 20 h) (endpointMeanCornerA 30 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 30 20, endpointRunWeightQ (endpointMeanCutoff 30 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 30 20) = (204106883/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 30 20 h = (logRoundedQ ((endpointMeanCutoff 30 20:ℚ)/200)).2+(204106883/500000000000000:ℚ)+((endpointMeanRuns 30 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 30 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 30 20) r*endpointJoint24Q (endpointMeanCornerK 30 20 h) (endpointMeanCornerA 30 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 30 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 30 20 h≤endpointMeanCorner 30 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 30 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint30_20

namespace EndpointAnalyticJoint30_21
private noncomputable def weights : IntegerLookupTree := (.branch 1324 (.branch 998 (.leaf (56637547600000:ℤ)) (.leaf (29499281100000:ℤ))) (.branch 1655 (.leaf (14669607500000:ℤ)) (.branch 2800 (.leaf (17344111000000:ℤ)) (.leaf (2277187000000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 144 (.branch 126 (.leaf (1981118671959076:ℤ)) (.leaf (2291947166163240:ℤ))) (.branch 155 (.leaf (2729299006060769:ℤ)) (.branch 173 (.leaf (3077129582142760:ℤ)) (.leaf (3855255825464211:ℤ))))), (.branch 144 (.branch 126 (.leaf (1994243155556560:ℤ)) (.leaf (2313813590967887:ℤ))) (.branch 155 (.leaf (2766466142338832:ℤ)) (.branch 173 (.leaf (3128695433598987:ℤ)) (.leaf (3945224313324748:ℤ))))), (.branch 144 (.branch 126 (.leaf (1991824318030821:ℤ)) (.leaf (2312259089906013:ℤ))) (.branch 155 (.leaf (2769539128325459:ℤ)) (.branch 173 (.leaf (3139092196176374:ℤ)) (.leaf (3986683205546679:ℤ))))), (.branch 144 (.branch 126 (.leaf (2005534344243698:ℤ)) (.leaf (2335300284132447:ℤ))) (.branch 155 (.leaf (2809211469028999:ℤ)) (.branch 173 (.leaf (3194727892717368:ℤ)) (.leaf (4086236403413350:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 30 21) 8000 (endpointMeanRuns 30 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 30 21, EndpointRunConditions (endpointMeanCutoff 30 21) (endpointMeanBox 30 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 30 21 h) (endpointMeanCornerA 30 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 21, endpointJoint24Q (endpointMeanCornerK 30 21 h) (endpointMeanCornerA 30 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 30 21, endpointRunWeightQ (endpointMeanCutoff 30 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 30 21) = (50853611/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 30 21 h = (logRoundedQ ((endpointMeanCutoff 30 21:ℚ)/200)).2+(50853611/125000000000000:ℚ)+((endpointMeanRuns 30 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 30 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 30 21) r*endpointJoint24Q (endpointMeanCornerK 30 21 h) (endpointMeanCornerA 30 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 30 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 30 21 h≤endpointMeanCorner 30 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 30 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint30_21

namespace EndpointAnalyticJoint30_22
private noncomputable def weights : IntegerLookupTree := (.branch 1120 (.branch 847 (.leaf (27924717300000:ℤ)) (.leaf (33608032200000:ℤ))) (.branch 1655 (.leaf (34905775000000:ℤ)) (.branch 2800 (.leaf (17256329700000:ℤ)) (.leaf (2267886000000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 144 (.branch 126 (.leaf (1994243155556560:ℤ)) (.leaf (2313813590967887:ℤ))) (.branch 165 (.leaf (2766466142338832:ℤ)) (.branch 186 (.leaf (3539748662464274:ℤ)) (.leaf (4817151762791299:ℤ))))), (.branch 144 (.branch 126 (.leaf (2007454586025094:ℤ)) (.leaf (2335888633379785:ℤ))) (.branch 165 (.leaf (2804139414447393:ℤ)) (.branch 186 (.leaf (3611101331316278:ℤ)) (.leaf (4959837418055887:ℤ))))), (.branch 144 (.branch 126 (.leaf (2005534344243698:ℤ)) (.leaf (2335300284132447:ℤ))) (.branch 165 (.leaf (2809211469028999:ℤ)) (.branch 186 (.leaf (3639481111658151:ℤ)) (.leaf (5075992868773097:ℤ))))), (.branch 144 (.branch 126 (.leaf (2019338738628030:ℤ)) (.leaf (2358571079199766:ℤ))) (.branch 165 (.leaf (2849452097286523:ℤ)) (.branch 186 (.leaf (3717536324948940:ℤ)) (.leaf (5238794074366730:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 30 22) 8000 (endpointMeanRuns 30 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 30 22, EndpointRunConditions (endpointMeanCutoff 30 22) (endpointMeanBox 30 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 30 22 h) (endpointMeanCornerA 30 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 22, endpointJoint24Q (endpointMeanCornerK 30 22 h) (endpointMeanCornerA 30 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 30 22, endpointRunWeightQ (endpointMeanCutoff 30 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 30 22) = (202815319/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 30 22 h = (logRoundedQ ((endpointMeanCutoff 30 22:ℚ)/200)).2+(202815319/500000000000000:ℚ)+((endpointMeanRuns 30 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 30 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 30 22) r*endpointJoint24Q (endpointMeanCornerK 30 22 h) (endpointMeanCornerA 30 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 30 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 30 22 h≤endpointMeanCorner 30 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 30 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint30_22

namespace EndpointAnalyticJoint30_23
private noncomputable def weights : IntegerLookupTree := (.branch 1324 (.branch 998 (.leaf (51583213300000:ℤ)) (.leaf (29068380100000:ℤ))) (.branch 1655 (.leaf (14486449600000:ℤ)) (.branch 2800 (.leaf (17157114500000:ℤ)) (.leaf (2257373500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 144 (.branch 126 (.leaf (2007454586025094:ℤ)) (.leaf (2335888633379785:ℤ))) (.branch 155 (.leaf (2804139414447393:ℤ)) (.branch 173 (.leaf (3181125414096717:ℤ)) (.leaf (4037292358043344:ℤ))))), (.branch 144 (.branch 126 (.leaf (2020753539368926:ℤ)) (.leaf (2358174283724568:ℤ))) (.branch 155 (.leaf (2842325714859342:ℤ)) (.branch 173 (.leaf (3234434004517765:ℤ)) (.leaf (4131508956097592:ℤ))))), (.branch 144 (.branch 126 (.leaf (2019338738628030:ℤ)) (.leaf (2358571079199766:ℤ))) (.branch 155 (.leaf (2849452097286523:ℤ)) (.branch 173 (.leaf (3251349648455148:ℤ)) (.leaf (4188275587423005:ℤ))))), (.branch 144 (.branch 126 (.leaf (2033238150734130:ℤ)) (.leaf (2382073763033912:ℤ))) (.branch 155 (.leaf (2890269153548994:ℤ)) (.branch 173 (.leaf (3308974939808630:ℤ)) (.leaf (4292862836215370:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 30 23) 8000 (endpointMeanRuns 30 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 30 23, EndpointRunConditions (endpointMeanCutoff 30 23) (endpointMeanBox 30 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 30 23 h) (endpointMeanCornerA 30 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 23, endpointJoint24Q (endpointMeanCornerK 30 23 h) (endpointMeanCornerA 30 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 30 23, endpointRunWeightQ (endpointMeanCutoff 30 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 30 23) = (404276309/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 30 23 h = (logRoundedQ ((endpointMeanCutoff 30 23:ℚ)/200)).2+(404276309/1000000000000000:ℚ)+((endpointMeanRuns 30 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 30 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 30 23) r*endpointJoint24Q (endpointMeanCornerK 30 23 h) (endpointMeanCornerA 30 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 30 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 30 23 h≤endpointMeanCorner 30 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 30 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint30_23

namespace EndpointAnalyticJoint30_24
private noncomputable def weights : IntegerLookupTree := (.branch 1655 (.branch 1087 (.leaf (63590072600000:ℤ)) (.leaf (38982544600000:ℤ))) (.branch 2800 (.leaf (17059053000000:ℤ)) (.leaf (2246983300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 144 (.branch 126 (.leaf (2020753539368926:ℤ)) (.leaf (2358174283724568:ℤ))) (.branch 167 (.leaf (2842325714859342:ℤ)) (.leaf (3787392064659214:ℤ)))), (.branch 144 (.branch 126 (.leaf (2034140595408219:ℤ)) (.leaf (2380672551316679:ℤ))) (.branch 167 (.leaf (2881032029908088:ℤ)) (.leaf (3866588430223973:ℤ)))), (.branch 144 (.branch 126 (.leaf (2033238150734130:ℤ)) (.leaf (2382073763033912:ℤ))) (.branch 167 (.leaf (2890269153548994:ℤ)) (.leaf (3911017986799082:ℤ)))), (.branch 144 (.branch 126 (.leaf (2047233234583263:ℤ)) (.leaf (2405810646359554:ℤ))) (.branch 167 (.leaf (2931670894875486:ℤ)) (.leaf (3998146713282674:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 30 24) 8000 (endpointMeanRuns 30 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 30 24, EndpointRunConditions (endpointMeanCutoff 30 24) (endpointMeanBox 30 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 30 24 h) (endpointMeanCornerA 30 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 24, endpointJoint24Q (endpointMeanCornerK 30 24 h) (endpointMeanCornerA 30 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 30 24, endpointRunWeightQ (endpointMeanCutoff 30 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 30 24) = (402937729/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 30 24 h = (logRoundedQ ((endpointMeanCutoff 30 24:ℚ)/200)).2+(402937729/1000000000000000:ℚ)+((endpointMeanRuns 30 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 30 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 30 24) r*endpointJoint24Q (endpointMeanCornerK 30 24 h) (endpointMeanCornerA 30 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 30 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 30 24 h≤endpointMeanCorner 30 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 30 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint30_24

namespace EndpointAnalyticJoint30_25
private noncomputable def weights : IntegerLookupTree := (.branch 1655 (.branch 1120 (.leaf (66350755500000:ℤ)) (.leaf (34199056500000:ℤ))) (.branch 2800 (.leaf (16974174700000:ℤ)) (.leaf (2237989900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 144 (.branch 126 (.leaf (2034140595408219:ℤ)) (.leaf (2380672551316679:ℤ))) (.branch 165 (.leaf (2881032029908088:ℤ)) (.leaf (3758150546996112:ℤ)))), (.branch 144 (.branch 126 (.leaf (2047616337804312:ℤ)) (.leaf (2403385464640506:ℤ))) (.branch 165 (.leaf (2920265441065776:ℤ)) (.leaf (3833905663261655:ℤ)))), (.branch 144 (.branch 126 (.leaf (2047233234583263:ℤ)) (.leaf (2405810646359554:ℤ))) (.branch 165 (.leaf (2931670894875486:ℤ)) (.leaf (3878704757193267:ℤ)))), (.branch 144 (.branch 126 (.leaf (2061324648698414:ℤ)) (.leaf (2429784062927269:ℤ))) (.branch 165 (.leaf (2973665696603558:ℤ)) (.leaf (3961890551493706:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 30 25) 8000 (endpointMeanRuns 30 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 30 25, EndpointRunConditions (endpointMeanCutoff 30 25) (endpointMeanBox 30 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 30 25 h) (endpointMeanCornerA 30 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 30 25, endpointJoint24Q (endpointMeanCornerK 30 25 h) (endpointMeanCornerA 30 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 30 25, endpointRunWeightQ (endpointMeanCutoff 30 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 30 25) = (80355821/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 30 25 h = (logRoundedQ ((endpointMeanCutoff 30 25:ℚ)/200)).2+(80355821/200000000000000:ℚ)+((endpointMeanRuns 30 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 30 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 30 25) r*endpointJoint24Q (endpointMeanCornerK 30 25 h) (endpointMeanCornerA 30 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 30 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 30 25 h≤endpointMeanCorner 30 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 30 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint30_25

namespace EndpointAnalyticJoint31_10
private noncomputable def weights : IntegerLookupTree := (.branch 1066 (.leaf (102191792800000:ℤ)) (.branch 2164 (.leaf (75756154900000:ℤ)) (.leaf (13085423500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 133 (.leaf (1839484559450344:ℤ)) (.branch 167 (.leaf (2189274292579810:ℤ)) (.leaf (2896022825303342:ℤ)))), (.branch 133 (.leaf (1847353400214932:ℤ)) (.branch 167 (.leaf (2205279152143323:ℤ)) (.leaf (2936932326120345:ℤ)))), (.branch 133 (.leaf (1844481235396807:ℤ)) (.branch 167 (.leaf (2201779820110398:ℤ)) (.leaf (2941574765898601:ℤ)))), (.branch 133 (.leaf (1852680162938337:ℤ)) (.branch 167 (.leaf (2218652298396870:ℤ)) (.leaf (2985989182762262:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 31 10) 8000 (endpointMeanRuns 31 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 31 10, EndpointRunConditions (endpointMeanCutoff 31 10) (endpointMeanBox 31 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 31 10 h) (endpointMeanCornerA 31 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 10, endpointJoint24Q (endpointMeanCornerK 31 10 h) (endpointMeanCornerA 31 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 31 10, endpointRunWeightQ (endpointMeanCutoff 31 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 31 10) = (419168137/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 31 10 h = (logRoundedQ ((endpointMeanCutoff 31 10:ℚ)/200)).2+(419168137/1000000000000000:ℚ)+((endpointMeanRuns 31 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 31 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 31 10) r*endpointJoint24Q (endpointMeanCornerK 31 10 h) (endpointMeanCornerA 31 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 31 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 31 10 h≤endpointMeanCorner 31 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 31 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint31_10

namespace EndpointAnalyticJoint31_11
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 952 (.leaf (74140918800000:ℤ)) (.leaf (55923882000000:ℤ))) (.branch 2164 (.leaf (19445417000000:ℤ)) (.leaf (13031917700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 148 (.branch 133 (.leaf (1847353400214932:ℤ)) (.leaf (2205279152143323:ℤ))) (.branch 175 (.leaf (2481947080099738:ℤ)) (.leaf (3179517298922740:ℤ)))), (.branch 148 (.branch 133 (.leaf (1859781357852658:ℤ)) (.leaf (2230655263314019:ℤ))) (.branch 175 (.leaf (2520383175474507:ℤ)) (.leaf (3262002124321427:ℤ)))), (.branch 148 (.branch 133 (.leaf (1852680162938337:ℤ)) (.leaf (2218652298396870:ℤ))) (.branch 175 (.leaf (2505298953983285:ℤ)) (.leaf (3248073689603317:ℤ)))), (.branch 148 (.branch 133 (.leaf (1865632231057394:ℤ)) (.leaf (2245416084366547:ℤ))) (.branch 175 (.leaf (2546263488154993:ℤ)) (.leaf (3338805841628759:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 31 11) 8000 (endpointMeanRuns 31 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 31 11, EndpointRunConditions (endpointMeanCutoff 31 11) (endpointMeanBox 31 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 31 11 h) (endpointMeanCornerA 31 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 11, endpointJoint24Q (endpointMeanCornerK 31 11 h) (endpointMeanCornerA 31 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 31 11, endpointRunWeightQ (endpointMeanCutoff 31 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 31 11) = (83604917/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 31 11 h = (logRoundedQ ((endpointMeanCutoff 31 11:ℚ)/200)).2+(83604917/200000000000000:ℚ)+((endpointMeanRuns 31 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 31 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 31 11) r*endpointJoint24Q (endpointMeanCornerK 31 11 h) (endpointMeanCornerA 31 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 31 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 31 11 h≤endpointMeanCorner 31 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 31 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint31_11

namespace EndpointAnalyticJoint31_12
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 952 (.leaf (70578490800000:ℤ)) (.leaf (55471645300000:ℤ))) (.branch 2164 (.leaf (19319966200000:ℤ)) (.leaf (12961393500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 148 (.branch 133 (.leaf (1859781357852658:ℤ)) (.leaf (2230655263314019:ℤ))) (.branch 175 (.leaf (2520383175474507:ℤ)) (.leaf (3262002124321427:ℤ)))), (.branch 148 (.branch 133 (.leaf (1872292923819479:ℤ)) (.leaf (2256323376981324:ℤ))) (.branch 175 (.leaf (2559414502487981:ℤ)) (.leaf (3346626817436310:ℤ)))), (.branch 148 (.branch 133 (.leaf (1865632231057394:ℤ)) (.leaf (2245416084366547:ℤ))) (.branch 175 (.leaf (2546263488154993:ℤ)) (.leaf (3338805841628759:ℤ)))), (.branch 148 (.branch 133 (.leaf (1878674846952545:ℤ)) (.leaf (2272502724097468:ℤ))) (.branch 175 (.leaf (2587897839817834:ℤ)) (.leaf (3432072518482728:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 31 12) 8000 (endpointMeanRuns 31 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 31 12, EndpointRunConditions (endpointMeanCutoff 31 12) (endpointMeanBox 31 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 31 12 h) (endpointMeanCornerA 31 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 12, endpointJoint24Q (endpointMeanCornerK 31 12 h) (endpointMeanCornerA 31 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 31 12, endpointRunWeightQ (endpointMeanCutoff 31 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 31 12) = (104129327/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 31 12 h = (logRoundedQ ((endpointMeanCutoff 31 12:ℚ)/200)).2+(104129327/250000000000000:ℚ)+((endpointMeanRuns 31 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 31 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 31 12) r*endpointJoint24Q (endpointMeanCornerK 31 12 h) (endpointMeanCornerA 31 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 31 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 31 12 h≤endpointMeanCorner 31 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 31 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint31_12

namespace EndpointAnalyticJoint31_13
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 1006 (.leaf (78900783600000:ℤ)) (.leaf (44551480400000:ℤ))) (.branch 2164 (.leaf (19211528200000:ℤ)) (.leaf (12900433400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 148 (.branch 133 (.leaf (1872292923819479:ℤ)) (.leaf (2256323376981324:ℤ))) (.branch 171 (.leaf (2559414502487981:ℤ)) (.leaf (3202080034972501:ℤ)))), (.branch 148 (.branch 133 (.leaf (1884888660585353:ℤ)) (.leaf (2282286853213194:ℤ))) (.branch 171 (.leaf (2599050279056294:ℤ)) (.leaf (3279052479996009:ℤ)))), (.branch 148 (.branch 133 (.leaf (1878674846952545:ℤ)) (.leaf (2272502724097468:ℤ))) (.branch 171 (.leaf (2587897839817834:ℤ)) (.leaf (3273918965317849:ℤ)))), (.branch 148 (.branch 133 (.leaf (1891808643642361:ℤ)) (.leaf (2299916112201229:ℤ))) (.branch 171 (.leaf (2630212961262140:ℤ)) (.leaf (3358345097401680:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 31 13) 8000 (endpointMeanRuns 31 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 31 13, EndpointRunConditions (endpointMeanCutoff 31 13) (endpointMeanBox 31 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 31 13 h) (endpointMeanCornerA 31 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 13, endpointJoint24Q (endpointMeanCornerK 31 13 h) (endpointMeanCornerA 31 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 31 13, endpointRunWeightQ (endpointMeanCutoff 31 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 31 13) = (415214439/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 31 13 h = (logRoundedQ ((endpointMeanCutoff 31 13:ℚ)/200)).2+(415214439/1000000000000000:ℚ)+((endpointMeanRuns 31 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 31 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 31 13) r*endpointJoint24Q (endpointMeanCornerK 31 13 h) (endpointMeanCornerA 31 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 31 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 31 13 h≤endpointMeanCorner 31 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 31 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint31_13

namespace EndpointAnalyticJoint31_14
private noncomputable def weights : IntegerLookupTree := (.branch 1066 (.branch 861 (.leaf (45297503500000:ℤ)) (.leaf (26729024100000:ℤ))) (.branch 1488 (.leaf (34439243800000:ℤ)) (.branch 2164 (.leaf (19089083500000:ℤ)) (.leaf (12831599200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 148 (.branch 133 (.leaf (1884888660585353:ℤ)) (.leaf (2282286853213194:ℤ))) (.branch 167 (.leaf (2599050279056294:ℤ)) (.branch 183 (.leaf (3137622419805432:ℤ)) (.leaf (3789674003502587:ℤ))))), (.branch 148 (.branch 133 (.leaf (1897569134404201:ℤ)) (.leaf (2308549090741840:ℤ))) (.branch 167 (.leaf (2639299865846691:ℤ)) (.branch 183 (.leaf (3207521624193332:ℤ)) (.leaf (3904328130378492:ℤ))))), (.branch 148 (.branch 133 (.leaf (1891808643642361:ℤ)) (.leaf (2299916112201229:ℤ))) (.branch 167 (.leaf (2630212961262140:ℤ)) (.branch 183 (.leaf (3204476193228634:ℤ)) (.leaf (3926274364801738:ℤ))))), (.branch 148 (.branch 133 (.leaf (1905034258570854:ℤ)) (.leaf (2327660190270441:ℤ))) (.branch 167 (.leaf (2673219983860851:ℤ)) (.branch 183 (.leaf (3280801759949657:ℤ)) (.leaf (4055305595178086:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 31 14) 8000 (endpointMeanRuns 31 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 31 14, EndpointRunConditions (endpointMeanCutoff 31 14) (endpointMeanBox 31 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 31 14 h) (endpointMeanCornerA 31 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 14, endpointJoint24Q (endpointMeanCornerK 31 14 h) (endpointMeanCornerA 31 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 31 14, endpointRunWeightQ (endpointMeanCutoff 31 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 31 14) = (5171791/12500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 31 14 h = (logRoundedQ ((endpointMeanCutoff 31 14:ℚ)/200)).2+(5171791/12500000000000:ℚ)+((endpointMeanRuns 31 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 31 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 31 14) r*endpointJoint24Q (endpointMeanCornerK 31 14 h) (endpointMeanCornerA 31 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 31 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 31 14 h≤endpointMeanCorner 31 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 31 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint31_14

namespace EndpointAnalyticJoint31_15
private noncomputable def weights : IntegerLookupTree := (.branch 1253 (.branch 952 (.leaf (61099728300000:ℤ)) (.leaf (32041928800000:ℤ))) (.branch 1488 (.leaf (13369603800000:ℤ)) (.branch 2164 (.leaf (18968183900000:ℤ)) (.leaf (12763633500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 148 (.branch 133 (.leaf (1897569134404201:ℤ)) (.leaf (2308549090741840:ℤ))) (.branch 157 (.leaf (2639299865846691:ℤ)) (.branch 175 (.leaf (2882661705054283:ℤ)) (.leaf (3522519301586611:ℤ))))), (.branch 148 (.branch 133 (.leaf (1910334915339398:ℤ)) (.leaf (2335113527408612:ℤ))) (.branch 157 (.leaf (2680172768488206:ℤ)) (.branch 175 (.leaf (2935746236119826:ℤ)) (.leaf (3613902477785502:ℤ))))), (.branch 148 (.branch 133 (.leaf (1905034258570854:ℤ)) (.leaf (2327660190270441:ℤ))) (.branch 157 (.leaf (2673219983860851:ℤ)) (.branch 175 (.leaf (2931111110153833:ℤ)) (.leaf (3626494623514206:ℤ))))), (.branch 148 (.branch 133 (.leaf (1918352333638390:ℤ)) (.leaf (2355738947445488:ℤ))) (.branch 157 (.leaf (2716930220997718:ℤ)) (.branch 175 (.leaf (2988406615772876:ℤ)) (.leaf (3727797639684484:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 31 15) 8000 (endpointMeanRuns 31 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 31 15, EndpointRunConditions (endpointMeanCutoff 31 15) (endpointMeanBox 31 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 31 15 h) (endpointMeanCornerA 31 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 15, endpointJoint24Q (endpointMeanCornerK 31 15 h) (endpointMeanCornerA 31 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 31 15, endpointRunWeightQ (endpointMeanCutoff 31 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 31 15) = (82458137/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 31 15 h = (logRoundedQ ((endpointMeanCutoff 31 15:ℚ)/200)).2+(82458137/200000000000000:ℚ)+((endpointMeanRuns 31 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 31 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 31 15) r*endpointJoint24Q (endpointMeanCornerK 31 15 h) (endpointMeanCornerA 31 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 31 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 31 15 h≤endpointMeanCorner 31 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 31 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint31_15

namespace EndpointAnalyticJoint31_16
private noncomputable def weights : IntegerLookupTree := (.branch 1210 (.branch 952 (.leaf (58425625600000:ℤ)) (.leaf (27483428100000:ℤ))) (.branch 1742 (.leaf (29925210800000:ℤ)) (.branch 2856 (.leaf (14374687600000:ℤ)) (.leaf (2164894500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 141 (.branch 125 (.leaf (1910334915339398:ℤ)) (.leaf (2182305226335459:ℤ))) (.branch 159 (.leaf (2508322086325407:ℤ)) (.branch 175 (.leaf (2998824718587559:ℤ)) (.leaf (3613902477785502:ℤ))))), (.branch 141 (.branch 125 (.leaf (1923186577289378:ℤ)) (.leaf (2203601619303573:ℤ))) (.branch 159 (.leaf (2542193816366855:ℤ)) (.branch 175 (.leaf (3056198213544777:ℤ)) (.leaf (3707656367719994:ℤ))))), (.branch 141 (.branch 125 (.leaf (1918352333638390:ℤ)) (.leaf (2197548055607604:ℤ))) (.branch 159 (.leaf (2536322055364456:ℤ)) (.branch 175 (.leaf (3055973142932460:ℤ)) (.leaf (3727797639684484:ℤ))))), (.branch 141 (.branch 125 (.leaf (1931763515232860:ℤ)) (.leaf (2219958733752924:ℤ))) (.branch 159 (.leaf (2572356000878006:ℤ)) (.branch 175 (.leaf (3118116747924101:ℤ)) (.leaf (3831930468704520:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 31 16) 8000 (endpointMeanRuns 31 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 31 16, EndpointRunConditions (endpointMeanCutoff 31 16) (endpointMeanBox 31 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 31 16 h) (endpointMeanCornerA 31 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 16, endpointJoint24Q (endpointMeanCornerK 31 16 h) (endpointMeanCornerA 31 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 31 16, endpointRunWeightQ (endpointMeanCutoff 31 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 31 16) = (411034529/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 31 16 h = (logRoundedQ ((endpointMeanCutoff 31 16:ℚ)/200)).2+(411034529/1000000000000000:ℚ)+((endpointMeanRuns 31 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 31 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 31 16) r*endpointJoint24Q (endpointMeanCornerK 31 16 h) (endpointMeanCornerA 31 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 31 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 31 16 h≤endpointMeanCorner 31 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 31 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint31_16

namespace EndpointAnalyticJoint31_17
private noncomputable def weights : IntegerLookupTree := (.branch 1428 (.branch 861 (.leaf (37864614700000:ℤ)) (.branch 1066 (.leaf (26047797200000:ℤ)) (.leaf (29390809400000:ℤ)))) (.branch 1742 (.leaf (11586269300000:ℤ)) (.branch 2856 (.leaf (14291785700000:ℤ)) (.leaf (2154645100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 150 (.branch 125 (.leaf (1923186577289378:ℤ)) (.branch 141 (.leaf (2203601619303573:ℤ)) (.leaf (2542193816366855:ℤ)))) (.branch 167 (.leaf (2777312512204190:ℤ)) (.branch 183 (.leaf (3352026317293603:ℤ)) (.leaf (4144147688544083:ℤ))))), (.branch 150 (.branch 125 (.leaf (1936124698013441:ℤ)) (.branch 141 (.leaf (2225105836707961:ℤ)) (.leaf (2576522941454279:ℤ)))) (.branch 167 (.leaf (2822021210533337:ℤ)) (.branch 183 (.leaf (3426701960604638:ℤ)) (.leaf (4269526186651224:ℤ))))), (.branch 150 (.branch 125 (.leaf (1931763515232860:ℤ)) (.branch 141 (.leaf (2219958733752924:ℤ)) (.leaf (2572356000878006:ℤ)))) (.branch 167 (.leaf (2820270288159019:ℤ)) (.branch 183 (.leaf (3438950057906706:ℤ)) (.leaf (4326228675784398:ℤ))))), (.branch 150 (.branch 125 (.leaf (1945268454261044:ℤ)) (.branch 141 (.leaf (2242597956841175:ℤ)) (.leaf (2608901886595090:ℤ)))) (.branch 167 (.leaf (2868259043293246:ℤ)) (.branch 183 (.leaf (3520860422118389:ℤ)) (.leaf (4468403816149071:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 31 17) 8000 (endpointMeanRuns 31 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 31 17, EndpointRunConditions (endpointMeanCutoff 31 17) (endpointMeanBox 31 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 31 17 h) (endpointMeanCornerA 31 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 17, endpointJoint24Q (endpointMeanCornerK 31 17 h) (endpointMeanCornerA 31 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 31 17, endpointRunWeightQ (endpointMeanCutoff 31 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 31 17) = (102403877/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 31 17 h = (logRoundedQ ((endpointMeanCutoff 31 17:ℚ)/200)).2+(102403877/250000000000000:ℚ)+((endpointMeanRuns 31 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 31 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 31 17) r*endpointJoint24Q (endpointMeanCornerK 31 17 h) (endpointMeanCornerA 31 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 31 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 31 17 h≤endpointMeanCorner 31 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 31 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint31_17

namespace EndpointAnalyticJoint31_18
private noncomputable def weights : IntegerLookupTree := (.branch 1428 (.branch 861 (.leaf (35485484400000:ℤ)) (.branch 1066 (.leaf (25816460700000:ℤ)) (.leaf (29168572200000:ℤ)))) (.branch 1742 (.leaf (11510681800000:ℤ)) (.branch 2856 (.leaf (14209893200000:ℤ)) (.leaf (2144520500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 150 (.branch 125 (.leaf (1936124698013441:ℤ)) (.branch 141 (.leaf (2225105836707961:ℤ)) (.leaf (2576522941454279:ℤ)))) (.branch 167 (.leaf (2822021210533337:ℤ)) (.branch 183 (.leaf (3426701960604638:ℤ)) (.leaf (4269526186651224:ℤ))))), (.branch 150 (.branch 125 (.leaf (1949149859157741:ℤ)) (.branch 141 (.leaf (2246819906638387:ℤ)) (.leaf (2611315638131597:ℤ)))) (.branch 167 (.leaf (2867449621785501:ℤ)) (.branch 183 (.leaf (3503041210097751:ℤ)) (.leaf (4398697929828050:ℤ))))), (.branch 150 (.branch 125 (.leaf (1945268454261044:ℤ)) (.branch 141 (.leaf (2242597956841175:ℤ)) (.leaf (2608901886595090:ℤ)))) (.branch 167 (.leaf (2868259043293246:ℤ)) (.branch 183 (.leaf (3520860422118389:ℤ)) (.leaf (4468403816149071:ℤ))))), (.branch 150 (.branch 125 (.leaf (1958867806180202:ℤ)) (.branch 141 (.leaf (2265468055582310:ℤ)) (.leaf (2645966985734581:ℤ)))) (.branch 167 (.leaf (2917064358680229:ℤ)) (.branch 183 (.leaf (3604721761962845:ℤ)) (.leaf (4615251333323332:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 31 18) 8000 (endpointMeanRuns 31 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 31 18, EndpointRunConditions (endpointMeanCutoff 31 18) (endpointMeanBox 31 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 31 18 h) (endpointMeanCornerA 31 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 18, endpointJoint24Q (endpointMeanCornerK 31 18 h) (endpointMeanCornerA 31 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 31 18, endpointRunWeightQ (endpointMeanCutoff 31 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 31 18) = (204106883/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 31 18 h = (logRoundedQ ((endpointMeanCutoff 31 18:ℚ)/200)).2+(204106883/500000000000000:ℚ)+((endpointMeanRuns 31 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 31 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 31 18) r*endpointJoint24Q (endpointMeanCornerK 31 18 h) (endpointMeanCornerA 31 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 31 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 31 18 h≤endpointMeanCorner 31 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 31 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint31_18

namespace EndpointAnalyticJoint31_19
private noncomputable def weights : IntegerLookupTree := (.branch 1428 (.branch 904 (.leaf (41122098800000:ℤ)) (.branch 1134 (.leaf (26368096400000:ℤ)) (.leaf (20680199000000:ℤ)))) (.branch 1742 (.leaf (11436003600000:ℤ)) (.branch 2856 (.leaf (14128986000000:ℤ)) (.leaf (2134517700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 150 (.branch 125 (.leaf (1949149859157741:ℤ)) (.branch 141 (.leaf (2246819906638387:ℤ)) (.leaf (2611315638131597:ℤ)))) (.branch 163 (.leaf (2867449621785501:ℤ)) (.branch 179 (.leaf (3331053606713915:ℤ)) (.leaf (4136426881117373:ℤ))))), (.branch 150 (.branch 125 (.leaf (1962262646281404:ℤ)) (.branch 141 (.leaf (2268745876976045:ℤ)) (.leaf (2646578166349168:ℤ)))) (.branch 163 (.leaf (2913609331775318:ℤ)) (.branch 179 (.leaf (3399828187383077:ℤ)) (.leaf (4252279099368222:ℤ))))), (.branch 150 (.branch 125 (.leaf (1958867806180202:ℤ)) (.branch 141 (.leaf (2265468055582310:ℤ)) (.leaf (2645966985734581:ℤ)))) (.branch 163 (.leaf (2917064358680229:ℤ)) (.branch 179 (.leaf (3416415646759090:ℤ)) (.leaf (4313866270436142:ℤ))))), (.branch 150 (.branch 125 (.leaf (1972562231029895:ℤ)) (.branch 141 (.leaf (2288571384454970:ℤ)) (.leaf (2683558674847148:ℤ)))) (.branch 163 (.leaf (2966700128630090:ℤ)) (.branch 179 (.leaf (3491599504894696:ℤ)) (.leaf (4444502529389928:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 31 19) 8000 (endpointMeanRuns 31 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 31 19, EndpointRunConditions (endpointMeanCutoff 31 19) (endpointMeanBox 31 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 31 19 h) (endpointMeanCornerA 31 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 19, endpointJoint24Q (endpointMeanCornerK 31 19 h) (endpointMeanCornerA 31 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 31 19, endpointRunWeightQ (endpointMeanCutoff 31 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 31 19) = (50853611/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 31 19 h = (logRoundedQ ((endpointMeanCutoff 31 19:ℚ)/200)).2+(50853611/125000000000000:ℚ)+((endpointMeanRuns 31 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 31 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 31 19) r*endpointJoint24Q (endpointMeanCornerK 31 19 h) (endpointMeanCornerA 31 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 31 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 31 19 h≤endpointMeanCorner 31 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 31 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint31_19

namespace EndpointAnalyticJoint31_20
private noncomputable def weights : IntegerLookupTree := (.branch 1171 (.branch 928 (.leaf (43296530000000:ℤ)) (.leaf (26340255800000:ℤ))) (.branch 1742 (.leaf (33741671000000:ℤ)) (.branch 2856 (.leaf (14058981800000:ℤ)) (.leaf (2125863000000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 141 (.branch 125 (.leaf (1962262646281404:ℤ)) (.leaf (2268745876976045:ℤ))) (.branch 161 (.leaf (2646578166349168:ℤ)) (.branch 177 (.leaf (3315499920490004:ℤ)) (.leaf (4124481654702213:ℤ))))), (.branch 141 (.branch 125 (.leaf (1975463648882878:ℤ)) (.leaf (2290885815586741:ℤ))) (.branch 161 (.leaf (2682316870590098:ℤ)) (.branch 177 (.leaf (3381396665322553:ℤ)) (.leaf (4235652417872594:ℤ))))), (.branch 141 (.branch 125 (.leaf (1972562231029895:ℤ)) (.leaf (2288571384454970:ℤ))) (.branch 161 (.leaf (2683558674847148:ℤ)) (.branch 177 (.leaf (3399652879917654:ℤ)) (.leaf (4298790163953377:ℤ))))), (.branch 141 (.branch 125 (.leaf (1986352393464011:ℤ)) (.leaf (2311910321948854:ℤ))) (.branch 161 (.leaf (2721684435283336:ℤ)) (.branch 177 (.leaf (3471570200238963:ℤ)) (.leaf (4423805538353472:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 31 20) 8000 (endpointMeanRuns 31 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 31 20, EndpointRunConditions (endpointMeanCutoff 31 20) (endpointMeanBox 31 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 31 20 h) (endpointMeanCornerA 31 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 20, endpointJoint24Q (endpointMeanCornerK 31 20 h) (endpointMeanCornerA 31 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 31 20, endpointRunWeightQ (endpointMeanCutoff 31 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 31 20) = (202815319/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 31 20 h = (logRoundedQ ((endpointMeanCutoff 31 20:ℚ)/200)).2+(202815319/500000000000000:ℚ)+((endpointMeanRuns 31 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 31 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 31 20) r*endpointJoint24Q (endpointMeanCornerK 31 20 h) (endpointMeanCornerA 31 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 31 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 31 20 h≤endpointMeanCorner 31 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 31 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint31_20

namespace EndpointAnalyticJoint31_21
private noncomputable def weights : IntegerLookupTree := (.branch 1428 (.branch 1066 (.leaf (64780243600000:ℤ)) (.leaf (28544313600000:ℤ))) (.branch 1742 (.leaf (11298358300000:ℤ)) (.branch 2856 (.leaf (13979859300000:ℤ)) (.leaf (2116080800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 141 (.branch 125 (.leaf (1975463648882878:ℤ)) (.leaf (2290885815586741:ℤ))) (.branch 150 (.leaf (2682316870590098:ℤ)) (.branch 167 (.leaf (2960512112823874:ℤ)) (.leaf (3660859598963668:ℤ))))), (.branch 141 (.branch 125 (.leaf (1988753460426425:ℤ)) (.leaf (2313241810515889:ℤ))) (.branch 150 (.leaf (2718538181011733:ℤ)) (.branch 167 (.leaf (3008169926761052:ℤ)) (.leaf (3742415356510563:ℤ))))), (.branch 141 (.branch 125 (.leaf (1986352393464011:ℤ)) (.leaf (2311910321948854:ℤ))) (.branch 150 (.leaf (2721684435283336:ℤ)) (.branch 167 (.leaf (3017180483873786:ℤ)) (.leaf (3778484352017019:ℤ))))), (.branch 141 (.branch 125 (.leaf (2000238962783021:ℤ)) (.leaf (2335487270809581:ℤ))) (.branch 150 (.leaf (2760351854682476:ℤ)) (.branch 167 (.leaf (3068519795585966:ℤ)) (.leaf (3868481887378221:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 31 21) 8000 (endpointMeanRuns 31 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 31 21, EndpointRunConditions (endpointMeanCutoff 31 21) (endpointMeanBox 31 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 31 21 h) (endpointMeanCornerA 31 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 21, endpointJoint24Q (endpointMeanCornerK 31 21 h) (endpointMeanCornerA 31 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 31 21, endpointRunWeightQ (endpointMeanCutoff 31 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 31 21) = (404276309/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 31 21 h = (logRoundedQ ((endpointMeanCutoff 31 21:ℚ)/200)).2+(404276309/1000000000000000:ℚ)+((endpointMeanRuns 31 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 31 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 31 21) r*endpointJoint24Q (endpointMeanCornerK 31 21 h) (endpointMeanCornerA 31 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 31 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 31 21 h≤endpointMeanCorner 31 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 31 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint31_21

namespace EndpointAnalyticJoint31_22
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 1099 (.leaf (67313535200000:ℤ)) (.leaf (28124420600000:ℤ))) (.branch 2164 (.leaf (18189736300000:ℤ)) (.branch 2856 (.leaf (3675786700000:ℤ)) (.leaf (2106412400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 133 (.branch 125 (.leaf (1988753460426425:ℤ)) (.leaf (2313241810515889:ℤ))) (.branch 148 (.leaf (2501043890681686:ℤ)) (.branch 165 (.leaf (2939050970707770:ℤ)) (.leaf (3639481111658151:ℤ))))), (.branch 133 (.branch 125 (.leaf (2002132678368799:ℤ)) (.leaf (2335815970185453:ℤ))) (.branch 148 (.leaf (2529823361866114:ℤ)) (.branch 165 (.leaf (2984565899018370:ℤ)) (.leaf (3717536324948940:ℤ))))), (.branch 133 (.branch 125 (.leaf (2000238962783021:ℤ)) (.leaf (2335487270809581:ℤ))) (.branch 148 (.leaf (2531469280599795:ℤ)) (.branch 165 (.leaf (2994616392262372:ℤ)) (.leaf (3754627863314532:ℤ))))), (.branch 133 (.branch 125 (.leaf (2014222612966475:ℤ)) (.leaf (2359304658286074:ℤ))) (.branch 148 (.leaf (2562006603669185:ℤ)) (.branch 165 (.leaf (3043581832229903:ℤ)) (.leaf (3840586339919563:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 31 22) 8000 (endpointMeanRuns 31 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 31 22, EndpointRunConditions (endpointMeanCutoff 31 22) (endpointMeanBox 31 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 31 22 h) (endpointMeanCornerA 31 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 22, endpointJoint24Q (endpointMeanCornerK 31 22 h) (endpointMeanCornerA 31 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 31 22, endpointRunWeightQ (endpointMeanCutoff 31 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 31 22) = (402937729/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 31 22 h = (logRoundedQ ((endpointMeanCutoff 31 22:ℚ)/200)).2+(402937729/1000000000000000:ℚ)+((endpointMeanRuns 31 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 31 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 31 22) r*endpointJoint24Q (endpointMeanCornerK 31 22 h) (endpointMeanCornerA 31 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 31 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 31 22 h≤endpointMeanCorner 31 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 31 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint31_22

namespace EndpointAnalyticJoint31_23
private noncomputable def weights : IntegerLookupTree := (.branch 1587 (.branch 1134 (.leaf (70330845100000:ℤ)) (.leaf (29582915000000:ℤ))) (.branch 2856 (.leaf (21889277800000:ℤ)) (.leaf (2098043900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 145 (.branch 125 (.leaf (2002132678368799:ℤ)) (.leaf (2335815970185453:ℤ))) (.branch 163 (.leaf (2882169864833826:ℤ)) (.leaf (3614789527073401:ℤ)))), (.branch 145 (.branch 125 (.leaf (2015601904186113:ℤ)) (.leaf (2358610423592775:ℤ))) (.branch 163 (.leaf (2924271308261081:ℤ)) (.leaf (3689422259921251:ℤ)))), (.branch 145 (.branch 125 (.leaf (2014222612966475:ℤ)) (.leaf (2359304658286074:ℤ))) (.branch 163 (.leaf (2934324065661197:ℤ)) (.leaf (3727224792938406:ℤ)))), (.branch 145 (.branch 125 (.leaf (2028304022705711:ℤ)) (.leaf (2383364936380422:ℤ))) (.branch 163 (.leaf (2979509648809797:ℤ)) (.leaf (3809248518692507:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 31 23) 8000 (endpointMeanRuns 31 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 31 23, EndpointRunConditions (endpointMeanCutoff 31 23) (endpointMeanBox 31 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 31 23 h) (endpointMeanCornerA 31 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 23, endpointJoint24Q (endpointMeanCornerK 31 23 h) (endpointMeanCornerA 31 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 31 23, endpointRunWeightQ (endpointMeanCutoff 31 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 31 23) = (80355821/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 31 23 h = (logRoundedQ ((endpointMeanCutoff 31 23:ℚ)/200)).2+(80355821/200000000000000:ℚ)+((endpointMeanRuns 31 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 31 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 31 23) r*endpointJoint24Q (endpointMeanCornerK 31 23 h) (endpointMeanCornerA 31 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 31 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 31 23 h≤endpointMeanCorner 31 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 31 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint31_23

namespace EndpointAnalyticJoint31_24
private noncomputable def weights : IntegerLookupTree := (.branch 1587 (.branch 1134 (.leaf (67392199900000:ℤ)) (.leaf (29374625600000:ℤ))) (.branch 2856 (.leaf (21763537200000:ℤ)) (.leaf (2088581800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 145 (.branch 125 (.leaf (2015601904186113:ℤ)) (.leaf (2358610423592775:ℤ))) (.branch 163 (.leaf (2924271308261081:ℤ)) (.leaf (3689422259921251:ℤ)))), (.branch 145 (.branch 125 (.leaf (2029161743400867:ℤ)) (.leaf (2381627320511393:ℤ))) (.branch 163 (.leaf (2966987750672369:ℤ)) (.leaf (3765595897093024:ℤ)))), (.branch 145 (.branch 125 (.leaf (2028304022705711:ℤ)) (.leaf (2383364936380422:ℤ))) (.branch 163 (.leaf (2979509648809797:ℤ)) (.leaf (3809248518692507:ℤ)))), (.branch 145 (.branch 125 (.leaf (2042483875436783:ℤ)) (.leaf (2407670582100337:ℤ))) (.branch 163 (.leaf (3025391043627041:ℤ)) (.leaf (3893077311744764:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 31 24) 8000 (endpointMeanRuns 31 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 31 24, EndpointRunConditions (endpointMeanCutoff 31 24) (endpointMeanBox 31 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 31 24 h) (endpointMeanCornerA 31 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 24, endpointJoint24Q (endpointMeanCornerK 31 24 h) (endpointMeanCornerA 31 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 31 24, endpointRunWeightQ (endpointMeanCutoff 31 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 31 24) = (200234543/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 31 24 h = (logRoundedQ ((endpointMeanCutoff 31 24:ℚ)/200)).2+(200234543/500000000000000:ℚ)+((endpointMeanRuns 31 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 31 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 31 24) r*endpointJoint24Q (endpointMeanCornerK 31 24 h) (endpointMeanCornerA 31 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 31 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 31 24 h≤endpointMeanCorner 31 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 31 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint31_24

namespace EndpointAnalyticJoint31_25
private noncomputable def weights : IntegerLookupTree := (.branch 1587 (.branch 1134 (.leaf (64559386200000:ℤ)) (.leaf (29168679800000:ℤ))) (.branch 2856 (.leaf (21639211300000:ℤ)) (.leaf (2079226200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 145 (.branch 125 (.leaf (2029161743400867:ℤ)) (.leaf (2381627320511393:ℤ))) (.branch 163 (.leaf (2966987750672369:ℤ)) (.leaf (3765595897093024:ℤ)))), (.branch 145 (.branch 125 (.leaf (2042812805609184:ℤ)) (.leaf (2404868831693753:ℤ))) (.branch 163 (.leaf (3010328175696729:ℤ)) (.leaf (3843342252861691:ℤ)))), (.branch 145 (.branch 125 (.leaf (2042483875436783:ℤ)) (.leaf (2407670582100337:ℤ))) (.branch 163 (.leaf (3025391043627041:ℤ)) (.leaf (3893077311744764:ℤ)))), (.branch 145 (.branch 125 (.leaf (2056762859373643:ℤ)) (.leaf (2432224097714131:ℤ))) (.branch 163 (.leaf (3071978964899479:ℤ)) (.leaf (3978750895576645:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 31 25) 8000 (endpointMeanRuns 31 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 31 25, EndpointRunConditions (endpointMeanCutoff 31 25) (endpointMeanBox 31 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 31 25 h) (endpointMeanCornerA 31 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 25, endpointJoint24Q (endpointMeanCornerK 31 25 h) (endpointMeanCornerA 31 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 31 25, endpointRunWeightQ (endpointMeanCutoff 31 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 31 25) = (24948363/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 31 25 h = (logRoundedQ ((endpointMeanCutoff 31 25:ℚ)/200)).2+(24948363/62500000000000:ℚ)+((endpointMeanRuns 31 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 31 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 31 25) r*endpointJoint24Q (endpointMeanCornerK 31 25 h) (endpointMeanCornerA 31 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 31 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 31 25 h≤endpointMeanCorner 31 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 31 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint31_25

namespace EndpointAnalyticJoint31_26
private noncomputable def weights : IntegerLookupTree := (.branch 1347 (.leaf (92175994100000:ℤ)) (.branch 2856 (.leaf (42880870900000:ℤ)) (.leaf (2071125500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2042812805609184:ℤ)) (.branch 153 (.leaf (2404868831693753:ℤ)) (.leaf (3335816742804359:ℤ)))), (.branch 125 (.leaf (2056555704508205:ℤ)) (.branch 153 (.leaf (2428337149075973:ℤ)) (.leaf (3392712548484436:ℤ)))), (.branch 125 (.leaf (2056762859373643:ℤ)) (.branch 153 (.leaf (2432224097714131:ℤ)) (.leaf (3422483482986465:ℤ)))), (.branch 125 (.leaf (2071141667541540:ℤ)) (.branch 153 (.leaf (2457028011008352:ℤ)) (.leaf (3484293026716596:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 31 26) 8000 (endpointMeanRuns 31 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 31 26, EndpointRunConditions (endpointMeanCutoff 31 26) (endpointMeanBox 31 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 31 26 h) (endpointMeanCornerA 31 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 31 26, endpointJoint24Q (endpointMeanCornerK 31 26 h) (endpointMeanCornerA 31 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 31 26, endpointRunWeightQ (endpointMeanCutoff 31 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 31 26) = (199026137/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 31 26 h = (logRoundedQ ((endpointMeanCutoff 31 26:ℚ)/200)).2+(199026137/500000000000000:ℚ)+((endpointMeanRuns 31 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 31 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 31 26) r*endpointJoint24Q (endpointMeanCornerK 31 26 h) (endpointMeanCornerA 31 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 31 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 31 26 h≤endpointMeanCorner 31 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 31 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint31_26

namespace EndpointAnalyticJoint32_10
private noncomputable def weights : IntegerLookupTree := (.branch 1095 (.leaf (101686954200000:ℤ)) (.branch 1709 (.leaf (46062257400000:ℤ)) (.leaf (40467766700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 141 (.leaf (1852486567991794:ℤ)) (.branch 164 (.leaf (2363083820769466:ℤ)) (.leaf (2897478644159058:ℤ)))), (.branch 141 (.leaf (1852680162938337:ℤ)) (.branch 164 (.leaf (2363583920726834:ℤ)) (.leaf (2898443562017531:ℤ)))), (.branch 141 (.leaf (1858104408488120:ℤ)) (.branch 164 (.leaf (2382764263979391:ℤ)) (.leaf (2947304822362482:ℤ)))), (.branch 141 (.leaf (1858306274120652:ℤ)) (.branch 164 (.leaf (2383295519987158:ℤ)) (.leaf (2948354976219738:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 32 10) 8000 (endpointMeanRuns 32 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 32 10, EndpointRunConditions (endpointMeanCutoff 32 10) (endpointMeanBox 32 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 32 10 h) (endpointMeanCornerA 32 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 10, endpointJoint24Q (endpointMeanCornerK 32 10 h) (endpointMeanCornerA 32 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 32 10, endpointRunWeightQ (endpointMeanCutoff 32 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 32 10) = (415957129/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 32 10 h = (logRoundedQ ((endpointMeanCutoff 32 10:ℚ)/200)).2+(415957129/1000000000000000:ℚ)+((endpointMeanRuns 32 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 32 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 32 10) r*endpointJoint24Q (endpointMeanCornerK 32 10 h) (endpointMeanCornerA 32 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 32 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 32 10 h≤endpointMeanCorner 32 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 32 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint32_10

namespace EndpointAnalyticJoint32_11
private noncomputable def weights : IntegerLookupTree := (.branch 898 (.leaf (57664843400000:ℤ)) (.branch 1709 (.leaf (89713637000000:ℤ)) (.leaf (40349057700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 141 (.leaf (1852680162938337:ℤ)) (.branch 178 (.leaf (2363583920726834:ℤ)) (.leaf (3359115631700626:ℤ)))), (.branch 141 (.leaf (1865632231057394:ℤ)) (.branch 178 (.leaf (2397163747088406:ℤ)) (.leaf (3458798121120630:ℤ)))), (.branch 141 (.leaf (1858306274120652:ℤ)) (.branch 178 (.leaf (2383295519987158:ℤ)) (.leaf (3453051174433743:ℤ)))), (.branch 141 (.leaf (1871813566953889:ℤ)) (.branch 178 (.leaf (2418981061098750:ℤ)) (.leaf (3564447231412507:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 32 11) 8000 (endpointMeanRuns 32 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 32 11, EndpointRunConditions (endpointMeanCutoff 32 11) (endpointMeanBox 32 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 32 11 h) (endpointMeanCornerA 32 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 11, endpointJoint24Q (endpointMeanCornerK 32 11 h) (endpointMeanCornerA 32 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 32 11, endpointRunWeightQ (endpointMeanCutoff 32 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 32 11) = (415214439/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 32 11 h = (logRoundedQ ((endpointMeanCutoff 32 11:ℚ)/200)).2+(415214439/1000000000000000:ℚ)+((endpointMeanRuns 32 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 32 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 32 11) r*endpointJoint24Q (endpointMeanCornerK 32 11 h) (endpointMeanCornerA 32 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 32 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 32 11 h≤endpointMeanCorner 32 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 32 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint32_11

namespace EndpointAnalyticJoint32_12
private noncomputable def weights : IntegerLookupTree := (.branch 1430 (.branch 947 (.leaf (65354016400000:ℤ)) (.leaf (51838747000000:ℤ))) (.branch 2802 (.leaf (36291707800000:ℤ)) (.leaf (2512444000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 149 (.branch 125 (.leaf (1865632231057394:ℤ)) (.leaf (2110144996790143:ℤ))) (.branch 174 (.leaf (2568990582019374:ℤ)) (.leaf (3300709520622921:ℤ)))), (.branch 149 (.branch 125 (.leaf (1878674846952545:ℤ)) (.leaf (2131664335237539:ℤ))) (.branch 174 (.leaf (2611842227007132:ℤ)) (.leaf (3391081530008798:ℤ)))), (.branch 149 (.branch 125 (.leaf (1871813566953889:ℤ)) (.leaf (2121951249011829:ℤ))) (.branch 174 (.leaf (2598904984558083:ℤ)) (.leaf (3388003977462912:ℤ)))), (.branch 149 (.branch 125 (.leaf (1885419038952867:ℤ)) (.leaf (2144587882764416:ℤ))) (.branch 174 (.leaf (2644805990008589:ℤ)) (.leaf (3488345994062127:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 32 12) 8000 (endpointMeanRuns 32 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 32 12, EndpointRunConditions (endpointMeanCutoff 32 12) (endpointMeanBox 32 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 32 12 h) (endpointMeanCornerA 32 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 12, endpointJoint24Q (endpointMeanCornerK 32 12 h) (endpointMeanCornerA 32 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 32 12, endpointRunWeightQ (endpointMeanCutoff 32 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 32 12) = (8278523/20000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 32 12 h = (logRoundedQ ((endpointMeanCutoff 32 12:ℚ)/200)).2+(8278523/20000000000000:ℚ)+((endpointMeanRuns 32 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 32 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 32 12) r*endpointJoint24Q (endpointMeanCornerK 32 12 h) (endpointMeanCornerA 32 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 32 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 32 12 h≤endpointMeanCorner 32 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 32 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint32_12

namespace EndpointAnalyticJoint32_13
private noncomputable def weights : IntegerLookupTree := (.branch 1430 (.branch 947 (.leaf (62116636800000:ℤ)) (.leaf (51421294400000:ℤ))) (.branch 2802 (.leaf (36062406000000:ℤ)) (.leaf (2500286100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 149 (.branch 125 (.leaf (1878674846952545:ℤ)) (.leaf (2131664335237539:ℤ))) (.branch 174 (.leaf (2611842227007132:ℤ)) (.leaf (3391081530008798:ℤ)))), (.branch 149 (.branch 125 (.leaf (1891808643642361:ℤ)) (.leaf (2153403128711922:ℤ))) (.branch 174 (.leaf (2655408652146681:ℤ)) (.leaf (3483927886206900:ℤ)))), (.branch 149 (.branch 125 (.leaf (1885419038952867:ℤ)) (.leaf (2144587882764416:ℤ))) (.branch 174 (.leaf (2644805990008589:ℤ)) (.leaf (3488345994062127:ℤ)))), (.branch 149 (.branch 125 (.leaf (1899123403743082:ℤ)) (.leaf (2167466000475648:ℤ))) (.branch 174 (.leaf (2691517683927461:ℤ)) (.leaf (3591659825441422:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 32 13) 8000 (endpointMeanRuns 32 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 32 13, EndpointRunConditions (endpointMeanCutoff 32 13) (endpointMeanBox 32 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 32 13 h) (endpointMeanCornerA 32 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 13, endpointJoint24Q (endpointMeanCornerK 32 13 h) (endpointMeanCornerA 32 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 32 13, endpointRunWeightQ (endpointMeanCutoff 32 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 32 13) = (20623563/50000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 32 13 h = (logRoundedQ ((endpointMeanCutoff 32 13:ℚ)/200)).2+(20623563/50000000000000:ℚ)+((endpointMeanRuns 32 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 32 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 32 13) r*endpointJoint24Q (endpointMeanCornerK 32 13 h) (endpointMeanCornerA 32 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 32 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 32 13 h≤endpointMeanCorner 32 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 32 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint32_13

namespace EndpointAnalyticJoint32_14
private noncomputable def weights : IntegerLookupTree := (.branch 1709 (.branch 1095 (.leaf (88209505500000:ℤ)) (.leaf (44926971400000:ℤ))) (.branch 2802 (.leaf (15772364900000:ℤ)) (.leaf (2488279900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 141 (.branch 125 (.leaf (1891808643642361:ℤ)) (.leaf (2153403128711922:ℤ))) (.branch 164 (.leaf (2465761400067014:ℤ)) (.leaf (3098031064744047:ℤ)))), (.branch 141 (.branch 125 (.leaf (1905034258570854:ℤ)) (.leaf (2175363615223948:ℤ))) (.branch 164 (.leaf (2500792878719928:ℤ)) (.leaf (3167568933355343:ℤ)))), (.branch 141 (.branch 125 (.leaf (1899123403743082:ℤ)) (.leaf (2167466000475648:ℤ))) (.branch 164 (.leaf (2491963123256949:ℤ)) (.leaf (3166087710597297:ℤ)))), (.branch 141 (.branch 125 (.leaf (1912927380137098:ℤ)) (.leaf (2190588178257444:ℤ))) (.branch 164 (.leaf (2529275765242710:ℤ)) (.leaf (3242181568309311:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 32 14) 8000 (endpointMeanRuns 32 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 32 14, EndpointRunConditions (endpointMeanCutoff 32 14) (endpointMeanBox 32 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 32 14 h) (endpointMeanCornerA 32 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 14, endpointJoint24Q (endpointMeanCornerK 32 14 h) (endpointMeanCornerA 32 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 32 14, endpointRunWeightQ (endpointMeanCutoff 32 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 32 14) = (411034529/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 32 14 h = (logRoundedQ ((endpointMeanCutoff 32 14:ℚ)/200)).2+(411034529/1000000000000000:ℚ)+((endpointMeanRuns 32 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 32 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 32 14) r*endpointJoint24Q (endpointMeanCornerK 32 14 h) (endpointMeanCornerA 32 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 32 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 32 14 h≤endpointMeanCorner 32 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 32 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint32_14

namespace EndpointAnalyticJoint32_15
private noncomputable def weights : IntegerLookupTree := (.branch 1430 (.branch 947 (.leaf (56018092800000:ℤ)) (.leaf (50601891200000:ℤ))) (.branch 1709 (.leaf (10724768300000:ℤ)) (.branch 2802 (.leaf (15680655200000:ℤ)) (.leaf (2476421700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 141 (.branch 125 (.leaf (1905034258570854:ℤ)) (.leaf (2175363615223948:ℤ))) (.branch 149 (.leaf (2500792878719928:ℤ)) (.branch 174 (.leaf (2699701780216376:ℤ)) (.leaf (3579316335770496:ℤ))))), (.branch 141 (.branch 125 (.leaf (1918352333638390:ℤ)) (.leaf (2197548055607604:ℤ))) (.branch 149 (.leaf (2536322055364456:ℤ)) (.branch 174 (.leaf (2744733732870610:ℤ)) (.leaf (3677316480124374:ℤ))))), (.branch 141 (.branch 125 (.leaf (1912927380137098:ℤ)) (.leaf (2190588178257444:ℤ))) (.branch 149 (.leaf (2529275765242710:ℤ)) (.branch 174 (.leaf (2739054384427918:ℤ)) (.leaf (3698033487403019:ℤ))))), (.branch 141 (.branch 125 (.leaf (1926831692172234:ℤ)) (.leaf (2213957019703288:ℤ))) (.branch 149 (.leaf (2567147096576228:ℤ)) (.branch 174 (.leaf (2787430662504979:ℤ)) (.leaf (3807557602500229:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 32 15) 8000 (endpointMeanRuns 32 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 32 15, EndpointRunConditions (endpointMeanCutoff 32 15) (endpointMeanBox 32 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 32 15 h) (endpointMeanCornerA 32 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 15, endpointJoint24Q (endpointMeanCornerK 32 15 h) (endpointMeanCornerA 32 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 32 15, endpointRunWeightQ (endpointMeanCutoff 32 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 32 15) = (102403877/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 32 15 h = (logRoundedQ ((endpointMeanCutoff 32 15:ℚ)/200)).2+(102403877/250000000000000:ℚ)+((endpointMeanRuns 32 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 32 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 32 15) r*endpointJoint24Q (endpointMeanCornerK 32 15 h) (endpointMeanCornerA 32 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 32 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 32 15 h≤endpointMeanCorner 32 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 32 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint32_15

namespace EndpointAnalyticJoint32_16
private noncomputable def weights : IntegerLookupTree := (.branch 1095 (.branch 922 (.leaf (48343127600000:ℤ)) (.leaf (20017513600000:ℤ))) (.branch 1709 (.leaf (44276426500000:ℤ)) (.branch 2802 (.leaf (15590062300000:ℤ)) (.leaf (2464707900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 141 (.branch 125 (.leaf (1918352333638390:ℤ)) (.leaf (2197548055607604:ℤ))) (.branch 164 (.leaf (2536322055364456:ℤ)) (.branch 176 (.leaf (3238667636919530:ℤ)) (.leaf (3779695198623871:ℤ))))), (.branch 141 (.branch 125 (.leaf (1931763515232860:ℤ)) (.leaf (2219958733752924:ℤ))) (.branch 164 (.leaf (2572356000878006:ℤ)) (.branch 176 (.leaf (3311362209667585:ℤ)) (.leaf (3887421489945781:ℤ))))), (.branch 141 (.branch 125 (.leaf (1926831692172234:ℤ)) (.leaf (2213957019703288:ℤ))) (.branch 164 (.leaf (2567147096576228:ℤ)) (.branch 176 (.leaf (3320104268337387:ℤ)) (.leaf (3923513975486365:ℤ))))), (.branch 141 (.branch 125 (.leaf (1940837069148556:ℤ)) (.leaf (2237575156181369:ℤ))) (.branch 164 (.leaf (2605585482620296:ℤ)) (.branch 176 (.leaf (3399899765138781:ℤ)) (.leaf (4044768849919106:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 32 16) 8000 (endpointMeanRuns 32 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 32 16, EndpointRunConditions (endpointMeanCutoff 32 16) (endpointMeanBox 32 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 32 16 h) (endpointMeanCornerA 32 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 16, endpointJoint24Q (endpointMeanCornerK 32 16 h) (endpointMeanCornerA 32 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 32 16, endpointRunWeightQ (endpointMeanCutoff 32 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 32 16) = (204106883/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 32 16 h = (logRoundedQ ((endpointMeanCutoff 32 16:ℚ)/200)).2+(204106883/500000000000000:ℚ)+((endpointMeanRuns 32 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 32 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 32 16) r*endpointJoint24Q (endpointMeanCornerK 32 16 h) (endpointMeanCornerA 32 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 32 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 32 16 h≤endpointMeanCorner 32 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 32 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint32_16

namespace EndpointAnalyticJoint32_17
private noncomputable def weights : IntegerLookupTree := (.branch 1322 (.branch 922 (.leaf (46026888500000:ℤ)) (.leaf (44371956600000:ℤ))) (.branch 1709 (.leaf (17928296900000:ℤ)) (.branch 2802 (.leaf (15511688400000:ℤ)) (.leaf (2454574100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 141 (.branch 125 (.leaf (1931763515232860:ℤ)) (.leaf (2219958733752924:ℤ))) (.branch 153 (.leaf (2572356000878006:ℤ)) (.branch 176 (.leaf (2913275544661827:ℤ)) (.leaf (3887421489945781:ℤ))))), (.branch 141 (.branch 125 (.leaf (1945268454261044:ℤ)) (.leaf (2242597956841175:ℤ))) (.branch 153 (.leaf (2608901886595090:ℤ)) (.branch 176 (.leaf (2965888868603590:ℤ)) (.leaf (3998218122454517:ℤ))))), (.branch 141 (.branch 125 (.leaf (1940837069148556:ℤ)) (.leaf (2237575156181369:ℤ))) (.branch 153 (.leaf (2605585482620296:ℤ)) (.branch 176 (.leaf (2967884954047440:ℤ)) (.leaf (4044768849919106:ℤ))))), (.branch 141 (.branch 125 (.leaf (1954944245667129:ℤ)) (.leaf (2261445247130894:ℤ))) (.branch 153 (.leaf (2644599413993904:ℤ)) (.branch 176 (.leaf (3024787113101994:ℤ)) (.leaf (4169771065298153:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 32 17) 8000 (endpointMeanRuns 32 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 32 17, EndpointRunConditions (endpointMeanCutoff 32 17) (endpointMeanBox 32 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 32 17 h) (endpointMeanCornerA 32 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 17, endpointJoint24Q (endpointMeanCornerK 32 17 h) (endpointMeanCornerA 32 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 32 17, endpointRunWeightQ (endpointMeanCutoff 32 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 32 17) = (40700109/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 32 17 h = (logRoundedQ ((endpointMeanCutoff 32 17:ℚ)/200)).2+(40700109/100000000000000:ℚ)+((endpointMeanRuns 32 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 32 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 32 17) r*endpointJoint24Q (endpointMeanCornerK 32 17 h) (endpointMeanCornerA 32 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 32 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 32 17 h≤endpointMeanCorner 32 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 32 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint32_17

namespace EndpointAnalyticJoint32_18
private noncomputable def weights : IntegerLookupTree := (.branch 1229 (.branch 1016 (.leaf (60597630600000:ℤ)) (.leaf (20038870400000:ℤ))) (.branch 1709 (.leaf (26339506700000:ℤ)) (.branch 2802 (.leaf (15423117600000:ℤ)) (.leaf (2443121800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 141 (.branch 125 (.leaf (1945268454261044:ℤ)) (.leaf (2242597956841175:ℤ))) (.branch 157 (.leaf (2608901886595090:ℤ)) (.branch 169 (.leaf (3106379448486876:ℤ)) (.leaf (3616982928445279:ℤ))))), (.branch 141 (.branch 125 (.leaf (1958867806180202:ℤ)) (.leaf (2265468055582310:ℤ))) (.branch 157 (.leaf (2645966985734581:ℤ)) (.branch 169 (.leaf (3167100988700454:ℤ)) (.leaf (3706619391943680:ℤ))))), (.branch 141 (.branch 125 (.leaf (1954944245667129:ℤ)) (.leaf (2261445247130894:ℤ))) (.branch 157 (.leaf (2644599413993904:ℤ)) (.branch 169 (.leaf (3176435897977748:ℤ)) (.leaf (3738276152468978:ℤ))))), (.branch 141 (.branch 125 (.leaf (1969153961668533:ℤ)) (.leaf (2285569980361535:ℤ))) (.branch 157 (.leaf (2684197508447704:ℤ)) (.branch 169 (.leaf (3242541860519110:ℤ)) (.leaf (3837944973598943:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 32 18) 8000 (endpointMeanRuns 32 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 32 18, EndpointRunConditions (endpointMeanCutoff 32 18) (endpointMeanBox 32 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 32 18 h) (endpointMeanCornerA 32 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 18, endpointJoint24Q (endpointMeanCornerK 32 18 h) (endpointMeanCornerA 32 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 32 18, endpointRunWeightQ (endpointMeanCutoff 32 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 32 18) = (202815319/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 32 18 h = (logRoundedQ ((endpointMeanCutoff 32 18:ℚ)/200)).2+(202815319/500000000000000:ℚ)+((endpointMeanRuns 32 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 32 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 32 18) r*endpointJoint24Q (endpointMeanCornerK 32 18 h) (endpointMeanCornerA 32 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 32 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 32 18 h≤endpointMeanCorner 32 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 32 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint32_18

namespace EndpointAnalyticJoint32_19
private noncomputable def weights : IntegerLookupTree := (.branch 1322 (.branch 973 (.leaf (50170324600000:ℤ)) (.leaf (34603698200000:ℤ))) (.branch 1709 (.leaf (17690879400000:ℤ)) (.branch 2802 (.leaf (15335588900000:ℤ)) (.leaf (2431804200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 141 (.branch 125 (.leaf (1958867806180202:ℤ)) (.leaf (2265468055582310:ℤ))) (.branch 153 (.leaf (2645966985734581:ℤ)) (.branch 172 (.leaf (3019452381366757:ℤ)) (.leaf (3870425778944289:ℤ))))), (.branch 141 (.branch 125 (.leaf (1972562231029895:ℤ)) (.leaf (2288571384454970:ℤ))) (.branch 153 (.leaf (2683558674847148:ℤ)) (.branch 172 (.leaf (3073983243220411:ℤ)) (.leaf (3972243606112277:ℤ))))), (.branch 141 (.branch 125 (.leaf (1969153961668533:ℤ)) (.leaf (2285569980361535:ℤ))) (.branch 153 (.leaf (2684197508447704:ℤ)) (.branch 172 (.leaf (3082780236178142:ℤ)) (.leaf (4022591634097670:ℤ))))), (.branch 141 (.branch 125 (.leaf (1983466962471678:ℤ)) (.leaf (2309952072356087:ℤ))) (.branch 153 (.leaf (2724388512767574:ℤ)) (.branch 172 (.leaf (3141885239925009:ℤ)) (.leaf (4136799847656049:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 32 19) 8000 (endpointMeanRuns 32 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 32 19, EndpointRunConditions (endpointMeanCutoff 32 19) (endpointMeanBox 32 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 32 19 h) (endpointMeanCornerA 32 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 19, endpointJoint24Q (endpointMeanCornerK 32 19 h) (endpointMeanCornerA 32 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 32 19, endpointRunWeightQ (endpointMeanCutoff 32 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 32 19) = (404276309/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 32 19 h = (logRoundedQ ((endpointMeanCutoff 32 19:ℚ)/200)).2+(404276309/1000000000000000:ℚ)+((endpointMeanRuns 32 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 32 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 32 19) r*endpointJoint24Q (endpointMeanCornerK 32 19 h) (endpointMeanCornerA 32 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 32 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 32 19 h≤endpointMeanCorner 32 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 32 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint32_19

namespace EndpointAnalyticJoint32_20
private noncomputable def weights : IntegerLookupTree := (.branch 1322 (.branch 1016 (.leaf (54989844500000:ℤ)) (.leaf (27779002100000:ℤ))) (.branch 1709 (.leaf (17574245300000:ℤ)) (.branch 2802 (.leaf (15249078000000:ℤ)) (.leaf (2420618200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 141 (.branch 125 (.leaf (1972562231029895:ℤ)) (.leaf (2288571384454970:ℤ))) (.branch 153 (.leaf (2683558674847148:ℤ)) (.branch 169 (.leaf (3073983243220411:ℤ)) (.leaf (3798477236009105:ℤ))))), (.branch 141 (.branch 125 (.leaf (1986352393464011:ℤ)) (.leaf (2311910321948854:ℤ))) (.branch 153 (.leaf (2721684435283336:ℤ)) (.branch 169 (.leaf (3129498924345547:ℤ)) (.leaf (3892611511135860:ℤ))))), (.branch 141 (.branch 125 (.leaf (1983466962471678:ℤ)) (.leaf (2309952072356087:ℤ))) (.branch 153 (.leaf (2724388512767574:ℤ)) (.branch 169 (.leaf (3141885239925009:ℤ)) (.leaf (3940271135572722:ℤ))))), (.branch 141 (.branch 125 (.leaf (1997883998812924:ℤ)) (.leaf (2334594268576338:ℤ))) (.branch 153 (.leaf (2765181304706711:ℤ)) (.branch 169 (.leaf (3202123442018920:ℤ)) (.leaf (4045325487631642:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 32 20) 8000 (endpointMeanRuns 32 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 32 20, EndpointRunConditions (endpointMeanCutoff 32 20) (endpointMeanBox 32 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 32 20 h) (endpointMeanCornerA 32 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 20, endpointJoint24Q (endpointMeanCornerK 32 20 h) (endpointMeanCornerA 32 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 32 20, endpointRunWeightQ (endpointMeanCutoff 32 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 32 20) = (402937729/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 32 20 h = (logRoundedQ ((endpointMeanCutoff 32 20:ℚ)/200)).2+(402937729/1000000000000000:ℚ)+((endpointMeanRuns 32 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 32 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 32 20) r*endpointJoint24Q (endpointMeanCornerK 32 20 h) (endpointMeanCornerA 32 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 32 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 32 20 h≤endpointMeanCorner 32 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 32 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint32_20

namespace EndpointAnalyticJoint32_21
private noncomputable def weights : IntegerLookupTree := (.branch 1229 (.branch 960 (.leaf (42895265400000:ℤ)) (.leaf (27395342300000:ℤ))) (.branch 1709 (.leaf (25807206000000:ℤ)) (.branch 2802 (.leaf (15163561500000:ℤ)) (.leaf (2409560800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 141 (.branch 125 (.leaf (1986352393464011:ℤ)) (.leaf (2311910321948854:ℤ))) (.branch 157 (.leaf (2721684435283336:ℤ)) (.branch 173 (.leaf (3292128109560201:ℤ)) (.leaf (4141885990415973:ℤ))))), (.branch 141 (.branch 125 (.leaf (2000238962783021:ℤ)) (.leaf (2335487270809581:ℤ))) (.branch 157 (.leaf (2760351854682476:ℤ)) (.branch 173 (.leaf (3356480547086873:ℤ)) (.leaf (4253042586896967:ℤ))))), (.branch 141 (.branch 125 (.leaf (1997883998812924:ℤ)) (.leaf (2334594268576338:ℤ))) (.branch 157 (.leaf (2765181304706711:ℤ)) (.branch 173 (.leaf (3378909682619097:ℤ)) (.leaf (4328711960133984:ℤ))))), (.branch 141 (.branch 125 (.leaf (2012405826885406:ℤ)) (.leaf (2359499343772232:ℤ))) (.branch 157 (.leaf (2806584894946598:ℤ)) (.branch 173 (.leaf (3449229400719527:ℤ)) (.leaf (4454230488122424:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 32 21) 8000 (endpointMeanRuns 32 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 32 21, EndpointRunConditions (endpointMeanCutoff 32 21) (endpointMeanBox 32 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 32 21 h) (endpointMeanCornerA 32 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 21, endpointJoint24Q (endpointMeanCornerK 32 21 h) (endpointMeanCornerA 32 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 32 21, endpointRunWeightQ (endpointMeanCutoff 32 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 32 21) = (80322907/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 32 21 h = (logRoundedQ ((endpointMeanCutoff 32 21:ℚ)/200)).2+(80322907/200000000000000:ℚ)+((endpointMeanRuns 32 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 32 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 32 21) r*endpointJoint24Q (endpointMeanCornerK 32 21 h) (endpointMeanCornerA 32 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 32 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 32 21 h≤endpointMeanCorner 32 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 32 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint32_21

namespace EndpointAnalyticJoint32_22
private noncomputable def weights : IntegerLookupTree := (.branch 1709 (.branch 1149 (.leaf (71528271200000:ℤ)) (.leaf (34899485000000:ℤ))) (.branch 2802 (.leaf (15089532500000:ℤ)) (.leaf (2399988800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 141 (.branch 125 (.leaf (2000238962783021:ℤ)) (.leaf (2335487270809581:ℤ))) (.branch 161 (.leaf (2760351854682476:ℤ)) (.leaf (3545008882047711:ℤ)))), (.branch 141 (.branch 125 (.leaf (2014222612966475:ℤ)) (.leaf (2359304658286074:ℤ))) (.branch 161 (.leaf (2799568628482738:ℤ)) (.leaf (3620001108700649:ℤ)))), (.branch 141 (.branch 125 (.leaf (2012405826885406:ℤ)) (.leaf (2359499343772232:ℤ))) (.branch 161 (.leaf (2806584894946598:ℤ)) (.leaf (3656537342305344:ℤ)))), (.branch 141 (.branch 125 (.leaf (2027033208378757:ℤ)) (.leaf (2384670102294289:ℤ))) (.branch 161 (.leaf (2848608429087396:ℤ)) (.leaf (3739149887287090:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 32 22) 8000 (endpointMeanRuns 32 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 32 22, EndpointRunConditions (endpointMeanCutoff 32 22) (endpointMeanBox 32 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 32 22 h) (endpointMeanCornerA 32 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 22, endpointJoint24Q (endpointMeanCornerK 32 22 h) (endpointMeanCornerA 32 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 32 22, endpointRunWeightQ (endpointMeanCutoff 32 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 32 22) = (200234543/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 32 22 h = (logRoundedQ ((endpointMeanCutoff 32 22:ℚ)/200)).2+(200234543/500000000000000:ℚ)+((endpointMeanRuns 32 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 32 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 32 22) r*endpointJoint24Q (endpointMeanCornerK 32 22 h) (endpointMeanCornerA 32 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 32 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 32 22 h≤endpointMeanCorner 32 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 32 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint32_22

namespace EndpointAnalyticJoint32_23
private noncomputable def weights : IntegerLookupTree := (.branch 1709 (.branch 1016 (.leaf (47648995100000:ℤ)) (.leaf (55546533000000:ℤ))) (.branch 2802 (.leaf (15005820200000:ℤ)) (.leaf (2389164700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 141 (.branch 125 (.leaf (2014222612966475:ℤ)) (.leaf (2359304658286074:ℤ))) (.branch 169 (.leaf (2799568628482738:ℤ)) (.leaf (4087936411696624:ℤ)))), (.branch 141 (.branch 125 (.leaf (2028304022705711:ℤ)) (.leaf (2383364936380422:ℤ))) (.branch 169 (.leaf (2839342561452650:ℤ)) (.leaf (4189244095531432:ℤ)))), (.branch 141 (.branch 125 (.leaf (2027033208378757:ℤ)) (.leaf (2384670102294289:ℤ))) (.branch 169 (.leaf (2848608429087396:ℤ)) (.leaf (4263911654141469:ℤ)))), (.branch 141 (.branch 125 (.leaf (2041766910519014:ℤ)) (.leaf (2410109378409384:ℤ))) (.branch 169 (.leaf (2891261189668075:ℤ)) (.leaf (4377594814677887:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 32 23) 8000 (endpointMeanRuns 32 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 32 23, EndpointRunConditions (endpointMeanCutoff 32 23) (endpointMeanBox 32 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 32 23 h) (endpointMeanCornerA 32 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 23, endpointJoint24Q (endpointMeanCornerK 32 23 h) (endpointMeanCornerA 32 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 32 23, endpointRunWeightQ (endpointMeanCutoff 32 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 32 23) = (24948363/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 32 23 h = (logRoundedQ ((endpointMeanCutoff 32 23:ℚ)/200)).2+(24948363/62500000000000:ℚ)+((endpointMeanRuns 32 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 32 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 32 23) r*endpointJoint24Q (endpointMeanCornerK 32 23 h) (endpointMeanCornerA 32 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 32 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 32 23 h≤endpointMeanCorner 32 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 32 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint32_23

namespace EndpointAnalyticJoint32_24
private noncomputable def weights : IntegerLookupTree := (.branch 1709 (.branch 1016 (.leaf (45280270500000:ℤ)) (.leaf (55143967700000:ℤ))) (.branch 2802 (.leaf (14923039400000:ℤ)) (.leaf (2378461000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 141 (.branch 125 (.leaf (2028304022705711:ℤ)) (.leaf (2383364936380422:ℤ))) (.branch 169 (.leaf (2839342561452650:ℤ)) (.leaf (4189244095531432:ℤ)))), (.branch 141 (.branch 125 (.leaf (2042483875436783:ℤ)) (.leaf (2407670582100337:ℤ))) (.branch 169 (.leaf (2879681569244377:ℤ)) (.leaf (4293062397382360:ℤ)))), (.branch 141 (.branch 125 (.leaf (2041766910519014:ℤ)) (.leaf (2410109378409384:ℤ))) (.branch 169 (.leaf (2891261189668075:ℤ)) (.leaf (4377594814677887:ℤ)))), (.branch 141 (.branch 125 (.leaf (2056607706108883:ℤ)) (.leaf (2435820036619905:ℤ))) (.branch 169 (.leaf (2934552598216854:ℤ)) (.leaf (4494308962260432:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 32 24) 8000 (endpointMeanRuns 32 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 32 24, EndpointRunConditions (endpointMeanCutoff 32 24) (endpointMeanBox 32 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 32 24 h) (endpointMeanCornerA 32 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 24, endpointJoint24Q (endpointMeanCornerK 32 24 h) (endpointMeanCornerA 32 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 32 24, endpointRunWeightQ (endpointMeanCutoff 32 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 32 24) = (397892943/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 32 24 h = (logRoundedQ ((endpointMeanCutoff 32 24:ℚ)/200)).2+(397892943/1000000000000000:ℚ)+((endpointMeanRuns 32 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 32 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 32 24) r*endpointJoint24Q (endpointMeanCornerK 32 24 h) (endpointMeanCornerA 32 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 32 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 32 24 h≤endpointMeanCorner 32 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 32 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint32_24

namespace EndpointAnalyticJoint32_25
private noncomputable def weights : IntegerLookupTree := (.branch 1229 (.leaf (74524173100000:ℤ)) (.branch 2802 (.leaf (59109382400000:ℤ)) (.leaf (2367875100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2042483875436783:ℤ)) (.branch 157 (.leaf (2407670582100337:ℤ)) (.leaf (3557184220890708:ℤ)))), (.branch 125 (.leaf (2056762859373643:ℤ)) (.branch 157 (.leaf (2432224097714131:ℤ)) (.leaf (3626717807594395:ℤ)))), (.branch 125 (.leaf (2056607706108883:ℤ)) (.branch 157 (.leaf (2435820036619905:ℤ)) (.leaf (3669091709700641:ℤ)))), (.branch 125 (.leaf (2071556373568259:ℤ)) (.branch 157 (.leaf (2461804971986286:ℤ)) (.leaf (3745450511487486:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 32 25) 8000 (endpointMeanRuns 32 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 32 25, EndpointRunConditions (endpointMeanCutoff 32 25) (endpointMeanBox 32 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 32 25 h) (endpointMeanCornerA 32 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 25, endpointJoint24Q (endpointMeanCornerK 32 25 h) (endpointMeanCornerA 32 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 32 25, endpointRunWeightQ (endpointMeanCutoff 32 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 32 25) = (99156543/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 32 25 h = (logRoundedQ ((endpointMeanCutoff 32 25:ℚ)/200)).2+(99156543/250000000000000:ℚ)+((endpointMeanRuns 32 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 32 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 32 25) r*endpointJoint24Q (endpointMeanCornerK 32 25 h) (endpointMeanCornerA 32 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 32 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 32 25 h≤endpointMeanCorner 32 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 32 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint32_25

namespace EndpointAnalyticJoint32_26
private noncomputable def weights : IntegerLookupTree := (.branch 1322 (.leaf (84078175900000:ℤ)) (.branch 2802 (.leaf (45319926200000:ℤ)) (.leaf (2357404400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2056762859373643:ℤ)) (.branch 153 (.leaf (2432224097714131:ℤ)) (.leaf (3422483482986465:ℤ)))), (.branch 125 (.leaf (2071141667541540:ℤ)) (.branch 153 (.leaf (2457028011008352:ℤ)) (.leaf (3484293026716596:ℤ)))), (.branch 125 (.leaf (2071556373568259:ℤ)) (.branch 153 (.leaf (2461804971986286:ℤ)) (.leaf (3521087599533478:ℤ)))), (.branch 125 (.leaf (2086613696975070:ℤ)) (.branch 153 (.leaf (2488067110452997:ℤ)) (.leaf (3588596108028880:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 32 26) 8000 (endpointMeanRuns 32 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 32 26, EndpointRunConditions (endpointMeanCutoff 32 26) (endpointMeanBox 32 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 32 26 h) (endpointMeanCornerA 32 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 32 26, endpointJoint24Q (endpointMeanCornerK 32 26 h) (endpointMeanCornerA 32 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 32 26, endpointRunWeightQ (endpointMeanCutoff 32 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 32 26) = (39537319/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 32 26 h = (logRoundedQ ((endpointMeanCutoff 32 26:ℚ)/200)).2+(39537319/100000000000000:ℚ)+((endpointMeanRuns 32 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 32 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 32 26) r*endpointJoint24Q (endpointMeanCornerK 32 26 h) (endpointMeanCornerA 32 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 32 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 32 26 h≤endpointMeanCorner 32 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 32 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint32_26

namespace EndpointAnalyticJoint33_11
private noncomputable def weights : IntegerLookupTree := (.branch 1127 (.leaf (99649023200000:ℤ)) (.branch 2750 (.leaf (84417853600000:ℤ)) (.leaf (2855178000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (1866818194930097:ℤ)) (.branch 161 (.leaf (2113659166502531:ℤ)) (.leaf (2900422014063571:ℤ)))), (.branch 125 (.leaf (1871813566953889:ℤ)) (.branch 161 (.leaf (2121951249011829:ℤ)) (.leaf (2924431122094024:ℤ)))), (.branch 125 (.leaf (1873146207506250:ℤ)) (.branch 161 (.leaf (2125955517564584:ℤ)) (.leaf (2954876813326947:ℤ)))), (.branch 125 (.leaf (1878360152258005:ℤ)) (.branch 161 (.leaf (2134688634848382:ℤ)) (.leaf (2981095289664311:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 33 11) 8000 (endpointMeanRuns 33 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 33 11, EndpointRunConditions (endpointMeanCutoff 33 11) (endpointMeanBox 33 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 33 11 h) (endpointMeanCornerA 33 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 11, endpointJoint24Q (endpointMeanCornerK 33 11 h) (endpointMeanCornerA 33 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 33 11, endpointRunWeightQ (endpointMeanCutoff 33 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 33 11) = (412110393/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 33 11 h = (logRoundedQ ((endpointMeanCutoff 33 11:ℚ)/200)).2+(412110393/1000000000000000:ℚ)+((endpointMeanRuns 33 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 33 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 33 11) r*endpointJoint24Q (endpointMeanCornerK 33 11 h) (endpointMeanCornerA 33 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 33 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 33 11 h≤endpointMeanCorner 33 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 33 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint33_11

namespace EndpointAnalyticJoint33_12
private noncomputable def weights : IntegerLookupTree := (.branch 1563 (.branch 1092 (.leaf (89766857800000:ℤ)) (.leaf (37226136800000:ℤ))) (.branch 2750 (.leaf (24230434500000:ℤ)) (.leaf (2844832200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 144 (.branch 125 (.leaf (1871813566953889:ℤ)) (.leaf (2121951249011829:ℤ))) (.branch 163 (.leaf (2483553433817075:ℤ)) (.leaf (2986921524562122:ℤ)))), (.branch 144 (.branch 125 (.leaf (1885419038952867:ℤ)) (.leaf (2144587882764416:ℤ))) (.branch 163 (.leaf (2523124215669881:ℤ)) (.leaf (3057243028527252:ℤ)))), (.branch 144 (.branch 125 (.leaf (1878360152258005:ℤ)) (.leaf (2134688634848382:ℤ))) (.branch 163 (.leaf (2510810711915164:ℤ)) (.leaf (3049015841017767:ℤ)))), (.branch 144 (.branch 125 (.leaf (1892563762867372:ℤ)) (.leaf (2158537402848972:ℤ))) (.branch 163 (.leaf (2553137091297675:ℤ)) (.leaf (3126154855754921:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 33 12) 8000 (endpointMeanRuns 33 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 33 12, EndpointRunConditions (endpointMeanCutoff 33 12) (endpointMeanBox 33 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 33 12 h) (endpointMeanCornerA 33 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 12, endpointJoint24Q (endpointMeanCornerK 33 12 h) (endpointMeanCornerA 33 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 33 12, endpointRunWeightQ (endpointMeanCutoff 33 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 33 12) = (411034529/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 33 12 h = (logRoundedQ ((endpointMeanCutoff 33 12:ℚ)/200)).2+(411034529/1000000000000000:ℚ)+((endpointMeanRuns 33 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 33 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 33 12) r*endpointJoint24Q (endpointMeanCornerK 33 12 h) (endpointMeanCornerA 33 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 33 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 33 12 h≤endpointMeanCorner 33 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 33 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint33_12

namespace EndpointAnalyticJoint33_13
private noncomputable def weights : IntegerLookupTree := (.branch 1563 (.branch 942 (.leaf (56911328100000:ℤ)) (.leaf (65106972300000:ℤ))) (.branch 2750 (.leaf (24102601500000:ℤ)) (.leaf (2832883200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 144 (.branch 125 (.leaf (1885419038952867:ℤ)) (.leaf (2144587882764416:ℤ))) (.branch 173 (.leaf (2523124215669881:ℤ)) (.leaf (3443869632101214:ℤ)))), (.branch 144 (.branch 125 (.leaf (1899123403743082:ℤ)) (.leaf (2167466000475648:ℤ))) (.branch 173 (.leaf (2563325483968086:ℤ)) (.leaf (3543730618645595:ℤ)))), (.branch 144 (.branch 125 (.leaf (1892563762867372:ℤ)) (.leaf (2158537402848972:ℤ))) (.branch 173 (.leaf (2553137091297675:ℤ)) (.leaf (3556204071770287:ℤ)))), (.branch 144 (.branch 125 (.leaf (1906874777029829:ℤ)) (.leaf (2182652609582524:ℤ))) (.branch 173 (.leaf (2596176994158137:ℤ)) (.leaf (3668368694601246:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 33 13) 8000 (endpointMeanRuns 33 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 33 13, EndpointRunConditions (endpointMeanCutoff 33 13) (endpointMeanBox 33 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 33 13 h) (endpointMeanCornerA 33 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 13, endpointJoint24Q (endpointMeanCornerK 33 13 h) (endpointMeanCornerA 33 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 33 13, endpointRunWeightQ (endpointMeanCutoff 33 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 33 13) = (102447983/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 33 13 h = (logRoundedQ ((endpointMeanCutoff 33 13:ℚ)/200)).2+(102447983/250000000000000:ℚ)+((endpointMeanRuns 33 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 33 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 33 13) r*endpointJoint24Q (endpointMeanCornerK 33 13 h) (endpointMeanCornerA 33 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 33 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 33 13 h≤endpointMeanCorner 33 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 33 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint33_13

namespace EndpointAnalyticJoint33_14
private noncomputable def weights : IntegerLookupTree := (.branch 1563 (.branch 1026 (.leaf (70407179400000:ℤ)) (.leaf (47499220800000:ℤ))) (.branch 2750 (.leaf (23958176600000:ℤ)) (.leaf (2819383200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 144 (.branch 125 (.leaf (1899123403743082:ℤ)) (.leaf (2167466000475648:ℤ))) (.branch 167 (.leaf (2563325483968086:ℤ)) (.leaf (3282287449105579:ℤ)))), (.branch 144 (.branch 125 (.leaf (1912927380137098:ℤ)) (.leaf (2190588178257444:ℤ))) (.branch 167 (.leaf (2604167284334727:ℤ)) (.leaf (3366230156795374:ℤ)))), (.branch 144 (.branch 125 (.leaf (1906874777029829:ℤ)) (.leaf (2182652609582524:ℤ))) (.branch 167 (.leaf (2596176994158137:ℤ)) (.leaf (3374395664746740:ℤ)))), (.branch 144 (.branch 125 (.leaf (1921294006899667:ℤ)) (.leaf (2207037231705890:ℤ))) (.branch 167 (.leaf (2639942448828781:ℤ)) (.leaf (3467541973105384:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 33 14) 8000 (endpointMeanRuns 33 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 33 14, EndpointRunConditions (endpointMeanCutoff 33 14) (endpointMeanBox 33 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 33 14 h) (endpointMeanCornerA 33 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 14, endpointJoint24Q (endpointMeanCornerK 33 14 h) (endpointMeanCornerA 33 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 33 14, endpointRunWeightQ (endpointMeanCutoff 33 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 33 14) = (204194027/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 33 14 h = (logRoundedQ ((endpointMeanCutoff 33 14:ℚ)/200)).2+(204194027/500000000000000:ℚ)+((endpointMeanRuns 33 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 33 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 33 14) r*endpointJoint24Q (endpointMeanCornerK 33 14 h) (endpointMeanCornerA 33 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 33 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 33 14 h≤endpointMeanCorner 33 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 33 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint33_14

namespace EndpointAnalyticJoint33_15
private noncomputable def weights : IntegerLookupTree := (.branch 1563 (.branch 1127 (.leaf (85807158300000:ℤ)) (.leaf (31567337600000:ℤ))) (.branch 2750 (.leaf (23815491800000:ℤ)) (.leaf (2806045800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 144 (.branch 125 (.leaf (1912927380137098:ℤ)) (.leaf (2190588178257444:ℤ))) (.branch 161 (.leaf (2604167284334727:ℤ)) (.leaf (3127159132447084:ℤ)))), (.branch 144 (.branch 125 (.leaf (1926831692172234:ℤ)) (.leaf (2213957019703288:ℤ))) (.branch 161 (.leaf (2645659822451070:ℤ)) (.leaf (3197811378085435:ℤ)))), (.branch 144 (.branch 125 (.leaf (1921294006899667:ℤ)) (.leaf (2207037231705890:ℤ))) (.branch 161 (.leaf (2639942448828781:ℤ)) (.leaf (3203082011278930:ℤ)))), (.branch 144 (.branch 125 (.leaf (1935822270772439:ℤ)) (.leaf (2231694279131148:ℤ))) (.branch 161 (.leaf (2684445686411317:ℤ)) (.leaf (3280691991428814:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 33 15) 8000 (endpointMeanRuns 33 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 33 15, EndpointRunConditions (endpointMeanCutoff 33 15) (endpointMeanBox 33 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 33 15 h) (endpointMeanCornerA 33 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 15, endpointJoint24Q (endpointMeanCornerK 33 15 h) (endpointMeanCornerA 33 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 33 15, endpointRunWeightQ (endpointMeanCutoff 33 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 33 15) = (40700109/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 33 15 h = (logRoundedQ ((endpointMeanCutoff 33 15:ℚ)/200)).2+(40700109/100000000000000:ℚ)+((endpointMeanRuns 33 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 33 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 33 15) r*endpointJoint24Q (endpointMeanCornerK 33 15 h) (endpointMeanCornerA 33 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 33 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 33 15 h≤endpointMeanCorner 33 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 33 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint33_15

namespace EndpointAnalyticJoint33_16
private noncomputable def weights : IntegerLookupTree := (.branch 1563 (.branch 1186 (.leaf (92453847100000:ℤ)) (.leaf (24257267300000:ℤ))) (.branch 2750 (.leaf (23674505700000:ℤ)) (.leaf (2792867300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 144 (.branch 125 (.leaf (1926831692172234:ℤ)) (.leaf (2213957019703288:ℤ))) (.branch 158 (.leaf (2645659822451070:ℤ)) (.leaf (3084298135890830:ℤ)))), (.branch 144 (.branch 125 (.leaf (1940837069148556:ℤ)) (.leaf (2237575156181369:ℤ))) (.branch 158 (.leaf (2687813466606832:ℤ)) (.leaf (3149817077530053:ℤ)))), (.branch 144 (.branch 125 (.leaf (1935822270772439:ℤ)) (.leaf (2231694279131148:ℤ))) (.branch 158 (.leaf (2684445686411317:ℤ)) (.leaf (3156328809894099:ℤ)))), (.branch 144 (.branch 125 (.leaf (1950460393131422:ℤ)) (.leaf (2256626795397165:ℤ))) (.branch 158 (.leaf (2729699144195130:ℤ)) (.leaf (3228032059827447:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 33 16) 8000 (endpointMeanRuns 33 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 33 16, EndpointRunConditions (endpointMeanCutoff 33 16) (endpointMeanBox 33 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 33 16 h) (endpointMeanCornerA 33 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 16, endpointJoint24Q (endpointMeanCornerK 33 16 h) (endpointMeanCornerA 33 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 33 16, endpointRunWeightQ (endpointMeanCutoff 33 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 33 16) = (202815319/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 33 16 h = (logRoundedQ ((endpointMeanCutoff 33 16:ℚ)/200)).2+(202815319/500000000000000:ℚ)+((endpointMeanRuns 33 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 33 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 33 16) r*endpointJoint24Q (endpointMeanCornerK 33 16 h) (endpointMeanCornerA 33 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 33 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 33 16 h≤endpointMeanCorner 33 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 33 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint33_16

namespace EndpointAnalyticJoint33_17
private noncomputable def weights : IntegerLookupTree := (.branch 1637 (.branch 1092 (.leaf (72778203700000:ℤ)) (.leaf (40621093800000:ℤ))) (.branch 2750 (.leaf (18902788900000:ℤ)) (.leaf (2779843700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 125 (.leaf (1940837069148556:ℤ)) (.leaf (2237575156181369:ℤ))) (.branch 163 (.leaf (2632448245412359:ℤ)) (.leaf (3355479320165839:ℤ)))), (.branch 142 (.branch 125 (.leaf (1954944245667129:ℤ)) (.leaf (2261445247130894:ℤ))) (.branch 163 (.leaf (2672690745156045:ℤ)) (.leaf (3434477830966201:ℤ)))), (.branch 142 (.branch 125 (.leaf (1950460393131422:ℤ)) (.leaf (2256626795397165:ℤ))) (.branch 163 (.leaf (2670905491391136:ℤ)) (.leaf (3454726833276400:ℤ)))), (.branch 142 (.branch 125 (.leaf (1965209204694383:ℤ)) (.leaf (2281837858045264:ℤ))) (.branch 163 (.leaf (2714050346901855:ℤ)) (.leaf (3542130191605951:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 33 17) 8000 (endpointMeanRuns 33 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 33 17, EndpointRunConditions (endpointMeanCutoff 33 17) (endpointMeanBox 33 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 33 17 h) (endpointMeanCornerA 33 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 17, endpointJoint24Q (endpointMeanCornerK 33 17 h) (endpointMeanCornerA 33 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 33 17, endpointRunWeightQ (endpointMeanCutoff 33 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 33 17) = (404276309/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 33 17 h = (logRoundedQ ((endpointMeanCutoff 33 17:ℚ)/200)).2+(404276309/1000000000000000:ℚ)+((endpointMeanRuns 33 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 33 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 33 17) r*endpointJoint24Q (endpointMeanCornerK 33 17 h) (endpointMeanCornerA 33 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 33 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 33 17 h≤endpointMeanCorner 33 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 33 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint33_17

namespace EndpointAnalyticJoint33_18
private noncomputable def weights : IntegerLookupTree := (.branch 1273 (.branch 882 (.leaf (32591056300000:ℤ)) (.leaf (47318368400000:ℤ))) (.branch 1637 (.leaf (19144514400000:ℤ)) (.branch 2750 (.leaf (18794226400000:ℤ)) (.leaf (2766971700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 125 (.leaf (1954944245667129:ℤ)) (.leaf (2261445247130894:ℤ))) (.branch 154 (.leaf (2672690745156045:ℤ)) (.branch 178 (.leaf (3061342700898688:ℤ)) (.leaf (4312481451784632:ℤ))))), (.branch 142 (.branch 125 (.leaf (1969153961668533:ℤ)) (.leaf (2285569980361535:ℤ))) (.branch 154 (.leaf (2713548436020183:ℤ)) (.branch 178 (.leaf (3121252510779450:ℤ)) (.leaf (4451602885338723:ℤ))))), (.branch 142 (.branch 125 (.leaf (1965209204694383:ℤ)) (.leaf (2281837858045264:ℤ))) (.branch 154 (.leaf (2714050346901855:ℤ)) (.branch 178 (.leaf (3131630016255093:ℤ)) (.leaf (4551968113064932:ℤ))))), (.branch 142 (.branch 125 (.leaf (1980069542460738:ℤ)) (.leaf (2307330578999085:ℤ))) (.branch 154 (.leaf (2757892149033503:ℤ)) (.branch 178 (.leaf (3196944500013839:ℤ)) (.leaf (4712945141133064:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 33 18) 8000 (endpointMeanRuns 33 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 33 18, EndpointRunConditions (endpointMeanCutoff 33 18) (endpointMeanBox 33 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 33 18 h) (endpointMeanCornerA 33 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 18, endpointJoint24Q (endpointMeanCornerK 33 18 h) (endpointMeanCornerA 33 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 33 18, endpointRunWeightQ (endpointMeanCutoff 33 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 33 18) = (402937729/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 33 18 h = (logRoundedQ ((endpointMeanCutoff 33 18:ℚ)/200)).2+(402937729/1000000000000000:ℚ)+((endpointMeanRuns 33 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 33 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 33 18) r*endpointJoint24Q (endpointMeanCornerK 33 18 h) (endpointMeanCornerA 33 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 33 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 33 18 h≤endpointMeanCorner 33 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 33 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint33_18

namespace EndpointAnalyticJoint33_19
private noncomputable def weights : IntegerLookupTree := (.branch 1273 (.branch 969 (.leaf (45637677700000:ℤ)) (.leaf (31066739700000:ℤ))) (.branch 1637 (.leaf (19016084800000:ℤ)) (.branch 2750 (.leaf (18686911700000:ℤ)) (.leaf (2754247500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 125 (.leaf (1969153961668533:ℤ)) (.leaf (2285569980361535:ℤ))) (.branch 154 (.leaf (2713548436020183:ℤ)) (.branch 171 (.leaf (3121252510779450:ℤ)) (.leaf (3959086448541099:ℤ))))), (.branch 142 (.branch 125 (.leaf (1983466962471678:ℤ)) (.leaf (2309952072356087:ℤ))) (.branch 154 (.leaf (2755030722492987:ℤ)) (.branch 171 (.leaf (3182334742590929:ℤ)) (.leaf (4069153760867170:ℤ))))), (.branch 142 (.branch 125 (.leaf (1980069542460738:ℤ)) (.leaf (2307330578999085:ℤ))) (.branch 154 (.leaf (2757892149033503:ℤ)) (.branch 171 (.leaf (3196944500013839:ℤ)) (.leaf (4135119265467491:ℤ))))), (.branch 142 (.branch 125 (.leaf (1995042249759053:ℤ)) (.leaf (2333108104948730:ℤ))) (.branch 154 (.leaf (2802442156013435:ℤ)) (.branch 171 (.leaf (3263621207843284:ℤ)) (.leaf (4259822737065303:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 33 19) 8000 (endpointMeanRuns 33 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 33 19, EndpointRunConditions (endpointMeanCutoff 33 19) (endpointMeanBox 33 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 33 19 h) (endpointMeanCornerA 33 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 19, endpointJoint24Q (endpointMeanCornerK 33 19 h) (endpointMeanCornerA 33 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 33 19, endpointRunWeightQ (endpointMeanCutoff 33 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 33 19) = (80322907/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 33 19 h = (logRoundedQ ((endpointMeanCutoff 33 19:ℚ)/200)).2+(80322907/200000000000000:ℚ)+((endpointMeanRuns 33 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 33 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 33 19) r*endpointJoint24Q (endpointMeanCornerK 33 19 h) (endpointMeanCornerA 33 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 33 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 33 19 h≤endpointMeanCorner 33 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 33 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint33_19

namespace EndpointAnalyticJoint33_20
private noncomputable def weights : IntegerLookupTree := (.branch 1273 (.branch 983 (.leaf (45582537300000:ℤ)) (.leaf (28656568400000:ℤ))) (.branch 1637 (.leaf (18889114700000:ℤ)) (.branch 2750 (.leaf (18580816500000:ℤ)) (.leaf (2741668000000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 125 (.leaf (1983466962471678:ℤ)) (.leaf (2309952072356087:ℤ))) (.branch 154 (.leaf (2755030722492987:ℤ)) (.branch 170 (.leaf (3182334742590929:ℤ)) (.leaf (4003679349825457:ℤ))))), (.branch 142 (.branch 125 (.leaf (1997883998812924:ℤ)) (.leaf (2334594268576338:ℤ))) (.branch 154 (.leaf (2797147152830028:ℤ)) (.branch 170 (.leaf (3244612340374936:ℤ)) (.leaf (4112678274499408:ℤ))))), (.branch 142 (.branch 125 (.leaf (1995042249759053:ℤ)) (.leaf (2333108104948730:ℤ))) (.branch 154 (.leaf (2802442156013435:ℤ)) (.branch 170 (.leaf (3263621207843284:ℤ)) (.leaf (4184277297071665:ℤ))))), (.branch 142 (.branch 125 (.leaf (2010128176294888:ℤ)) (.leaf (2359173617739155:ℤ))) (.branch 154 (.leaf (2847711807930386:ℤ)) (.branch 170 (.leaf (3331688550814176:ℤ)) (.leaf (4307685272769057:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 33 20) 8000 (endpointMeanRuns 33 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 33 20, EndpointRunConditions (endpointMeanCutoff 33 20) (endpointMeanBox 33 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 33 20 h) (endpointMeanCornerA 33 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 20, endpointJoint24Q (endpointMeanCornerK 33 20 h) (endpointMeanCornerA 33 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 33 20, endpointRunWeightQ (endpointMeanCutoff 33 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 33 20) = (400306377/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 33 20 h = (logRoundedQ ((endpointMeanCutoff 33 20:ℚ)/200)).2+(400306377/1000000000000000:ℚ)+((endpointMeanRuns 33 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 33 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 33 20) r*endpointJoint24Q (endpointMeanCornerK 33 20 h) (endpointMeanCornerA 33 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 33 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 33 20 h≤endpointMeanCorner 33 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 33 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint33_20

namespace EndpointAnalyticJoint33_21
private noncomputable def weights : IntegerLookupTree := (.branch 1433 (.branch 1026 (.leaf (50341782700000:ℤ)) (.leaf (35426615700000:ℤ))) (.branch 2084 (.leaf (20822975900000:ℤ)) (.leaf (14851542000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 148 (.branch 133 (.leaf (1997883998812924:ℤ)) (.leaf (2532606197935810:ℤ))) (.branch 167 (.leaf (3004891533957859:ℤ)) (.leaf (3916940477101794:ℤ)))), (.branch 148 (.branch 133 (.leaf (2012405826885406:ℤ)) (.leaf (2564676040852259:ℤ))) (.branch 167 (.leaf (3056883179144740:ℤ)) (.leaf (4017114089134849:ℤ)))), (.branch 148 (.branch 133 (.leaf (2010128176294888:ℤ)) (.leaf (2566947027000677:ℤ))) (.branch 167 (.leaf (3070928183261015:ℤ)) (.leaf (4082968792333679:ℤ)))), (.branch 148 (.branch 133 (.leaf (2025328178199040:ℤ)) (.leaf (2601119416602893:ℤ))) (.branch 167 (.leaf (3127297999136305:ℤ)) (.leaf (4195674446303856:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 33 21) 8000 (endpointMeanRuns 33 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 33 21, EndpointRunConditions (endpointMeanCutoff 33 21) (endpointMeanBox 33 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 33 21 h) (endpointMeanCornerA 33 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 21, endpointJoint24Q (endpointMeanCornerK 33 21 h) (endpointMeanCornerA 33 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 33 21, endpointRunWeightQ (endpointMeanCutoff 33 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 33 21) = (399012919/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 33 21 h = (logRoundedQ ((endpointMeanCutoff 33 21:ℚ)/200)).2+(399012919/1000000000000000:ℚ)+((endpointMeanRuns 33 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 33 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 33 21) r*endpointJoint24Q (endpointMeanCornerK 33 21 h) (endpointMeanCornerA 33 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 33 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 33 21 h≤endpointMeanCorner 33 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 33 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint33_21

namespace EndpointAnalyticJoint33_22
private noncomputable def weights : IntegerLookupTree := (.branch 1637 (.branch 1228 (.leaf (78863997100000:ℤ)) (.leaf (22762474100000:ℤ))) (.branch 2750 (.leaf (18372176000000:ℤ)) (.leaf (2716929900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 125 (.leaf (2012405826885406:ℤ)) (.leaf (2359499343772232:ℤ))) (.branch 156 (.leaf (2839907421252011:ℤ)) (.leaf (3400914962853848:ℤ)))), (.branch 142 (.branch 125 (.leaf (2027033208378757:ℤ)) (.leaf (2384670102294289:ℤ))) (.branch 156 (.leaf (2883321370176172:ℤ)) (.leaf (3470255919121811:ℤ)))), (.branch 142 (.branch 125 (.leaf (2025328178199040:ℤ)) (.leaf (2385530334762932:ℤ))) (.branch 156 (.leaf (2893712729672227:ℤ)) (.leaf (3503318347875289:ℤ)))), (.branch 142 (.branch 125 (.leaf (2040643118076109:ℤ)) (.leaf (2412181509357381:ℤ))) (.branch 156 (.leaf (2940456733911110:ℤ)) (.leaf (3579570852332809:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 33 22) 8000 (endpointMeanRuns 33 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 33 22, EndpointRunConditions (endpointMeanCutoff 33 22) (endpointMeanBox 33 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 33 22 h) (endpointMeanCornerA 33 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 22, endpointJoint24Q (endpointMeanCornerK 33 22 h) (endpointMeanCornerA 33 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 33 22, endpointRunWeightQ (endpointMeanCutoff 33 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 33 22) = (49716729/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 33 22 h = (logRoundedQ ((endpointMeanCutoff 33 22:ℚ)/200)).2+(49716729/125000000000000:ℚ)+((endpointMeanRuns 33 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 33 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 33 22) r*endpointJoint24Q (endpointMeanCornerK 33 22 h) (endpointMeanCornerA 33 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 33 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 33 22 h≤endpointMeanCorner 33 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 33 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint33_22

namespace EndpointAnalyticJoint33_23
private noncomputable def weights : IntegerLookupTree := (.branch 1637 (.branch 1273 (.leaf (82202484100000:ℤ)) (.leaf (18516638400000:ℤ))) (.branch 2750 (.leaf (18269578500000:ℤ)) (.leaf (2704765100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 125 (.leaf (2027033208378757:ℤ)) (.leaf (2384670102294289:ℤ))) (.branch 154 (.leaf (2883321370176172:ℤ)) (.leaf (3372847663864383:ℤ)))), (.branch 142 (.branch 125 (.leaf (2041766910519014:ℤ)) (.leaf (2410109378409384:ℤ))) (.branch 154 (.leaf (2927398992481751:ℤ)) (.leaf (3438853558023043:ℤ)))), (.branch 142 (.branch 125 (.leaf (2040643118076109:ℤ)) (.leaf (2412181509357381:ℤ))) (.branch 154 (.leaf (2940456733911110:ℤ)) (.leaf (3472111761583038:ℤ)))), (.branch 142 (.branch 125 (.leaf (2056073865053459:ℤ)) (.leaf (2439130431206147:ℤ))) (.branch 154 (.leaf (2987955824136887:ℤ)) (.leaf (3544527463975514:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 33 23) 8000 (endpointMeanRuns 33 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 33 23, EndpointRunConditions (endpointMeanCutoff 33 23) (endpointMeanBox 33 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 33 23 h) (endpointMeanCornerA 33 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 23, endpointJoint24Q (endpointMeanCornerK 33 23 h) (endpointMeanCornerA 33 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 33 23, endpointRunWeightQ (endpointMeanCutoff 33 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 33 23) = (198234401/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 33 23 h = (logRoundedQ ((endpointMeanCutoff 33 23:ℚ)/200)).2+(198234401/500000000000000:ℚ)+((endpointMeanRuns 33 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 33 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 33 23) r*endpointJoint24Q (endpointMeanCornerK 33 23 h) (endpointMeanCornerA 33 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 33 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 33 23 h≤endpointMeanCorner 33 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 33 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint33_23

namespace EndpointAnalyticJoint33_24
private noncomputable def weights : IntegerLookupTree := (.branch 1273 (.leaf (79124956500000:ℤ)) (.branch 2750 (.leaf (51837995900000:ℤ)) (.leaf (2692732500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2041766910519014:ℤ)) (.branch 154 (.leaf (2410109378409384:ℤ)) (.leaf (3438853558023043:ℤ)))), (.branch 125 (.leaf (2056607706108883:ℤ)) (.branch 154 (.leaf (2435820036619905:ℤ)) (.leaf (3506151173153973:ℤ)))), (.branch 125 (.leaf (2056073865053459:ℤ)) (.branch 154 (.leaf (2439130431206147:ℤ)) (.leaf (3544527463975514:ℤ)))), (.branch 125 (.leaf (2071621294830549:ℤ)) (.branch 154 (.leaf (2466380426745258:ℤ)) (.leaf (3618453496194061:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 33 24) 8000 (endpointMeanRuns 33 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 33 24, EndpointRunConditions (endpointMeanCutoff 33 24) (endpointMeanBox 33 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 33 24 h) (endpointMeanCornerA 33 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 24, endpointJoint24Q (endpointMeanCornerK 33 24 h) (endpointMeanCornerA 33 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 33 24, endpointRunWeightQ (endpointMeanCutoff 33 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 33 24) = (197608761/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 33 24 h = (logRoundedQ ((endpointMeanCutoff 33 24:ℚ)/200)).2+(197608761/500000000000000:ℚ)+((endpointMeanRuns 33 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 33 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 33 24) r*endpointJoint24Q (endpointMeanCornerK 33 24 h) (endpointMeanCornerA 33 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 33 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 33 24 h≤endpointMeanCorner 33 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 33 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint33_24

namespace EndpointAnalyticJoint33_25
private noncomputable def weights : IntegerLookupTree := (.branch 1186 (.leaf (64200989100000:ℤ)) (.branch 2750 (.leaf (65546512200000:ℤ)) (.leaf (2680829300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2056607706108883:ℤ)) (.branch 158 (.leaf (2435820036619905:ℤ)) (.leaf (3726637833152561:ℤ)))), (.branch 125 (.leaf (2071556373568259:ℤ)) (.branch 158 (.leaf (2461804971986286:ℤ)) (.leaf (3805801829609194:ℤ)))), (.branch 125 (.leaf (2071621294830549:ℤ)) (.branch 158 (.leaf (2466380426745258:ℤ)) (.leaf (3863515320200155:ℤ)))), (.branch 125 (.leaf (2087286289728606:ℤ)) (.branch 158 (.leaf (2493934859573735:ℤ)) (.leaf (3951283934090204:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 33 25) 8000 (endpointMeanRuns 33 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 33 25, EndpointRunConditions (endpointMeanCutoff 33 25) (endpointMeanBox 33 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 33 25 h) (endpointMeanCornerA 33 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 25, endpointJoint24Q (endpointMeanCornerK 33 25 h) (endpointMeanCornerA 33 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 33 25, endpointRunWeightQ (endpointMeanCutoff 33 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 33 25) = (393979697/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 33 25 h = (logRoundedQ ((endpointMeanCutoff 33 25:ℚ)/200)).2+(393979697/1000000000000000:ℚ)+((endpointMeanRuns 33 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 33 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 33 25) r*endpointJoint24Q (endpointMeanCornerK 33 25 h) (endpointMeanCornerA 33 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 33 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 33 25 h≤endpointMeanCorner 33 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 33 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint33_25

namespace EndpointAnalyticJoint33_26
private noncomputable def weights : IntegerLookupTree := (.branch 1322 (.leaf (79581262600000:ℤ)) (.branch 2750 (.leaf (44636751000000:ℤ)) (.leaf (2669052700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2071556373568259:ℤ)) (.branch 152 (.leaf (2461804971986286:ℤ)) (.leaf (3468907675711767:ℤ)))), (.branch 125 (.leaf (2086613696975070:ℤ)) (.branch 152 (.leaf (2488067110452997:ℤ)) (.leaf (3534065736308874:ℤ)))), (.branch 125 (.leaf (2087286289728606:ℤ)) (.branch 152 (.leaf (2493934859573735:ℤ)) (.leaf (3576997351332730:ℤ)))), (.branch 125 (.leaf (2103069738740732:ℤ)) (.branch 152 (.leaf (2521797130868764:ℤ)) (.leaf (3648488942945693:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 33 26) 8000 (endpointMeanRuns 33 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 33 26, EndpointRunConditions (endpointMeanCutoff 33 26) (endpointMeanBox 33 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 33 26 h) (endpointMeanCornerA 33 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 26, endpointJoint24Q (endpointMeanCornerK 33 26 h) (endpointMeanCornerA 33 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 33 26, endpointRunWeightQ (endpointMeanCutoff 33 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 33 26) = (392755041/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 33 26 h = (logRoundedQ ((endpointMeanCutoff 33 26:ℚ)/200)).2+(392755041/1000000000000000:ℚ)+((endpointMeanRuns 33 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 33 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 33 26) r*endpointJoint24Q (endpointMeanCornerK 33 26 h) (endpointMeanCornerA 33 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 33 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 33 26 h≤endpointMeanCorner 33 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 33 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint33_26

namespace EndpointAnalyticJoint33_27
private noncomputable def weights : IntegerLookupTree := (.branch 1228 (.leaf (64644705900000:ℤ)) (.branch 2750 (.leaf (57655254700000:ℤ)) (.leaf (2657400200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2086613696975070:ℤ)) (.branch 156 (.leaf (2488067110452997:ℤ)) (.leaf (3762048817136072:ℤ)))), (.branch 125 (.leaf (2101780466106395:ℤ)) (.branch 156 (.leaf (2514609409178012:ℤ)) (.leaf (3838752899818590:ℤ)))), (.branch 125 (.leaf (2103069738740732:ℤ)) (.branch 156 (.leaf (2521797130868764:ℤ)) (.leaf (3901543027567855:ℤ)))), (.branch 125 (.leaf (2118972537582318:ℤ)) (.branch 156 (.leaf (2549970679805518:ℤ)) (.leaf (3986463208253474:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 33 27) 8000 (endpointMeanRuns 33 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 33 27, EndpointRunConditions (endpointMeanCutoff 33 27) (endpointMeanBox 33 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 33 27 h) (endpointMeanCornerA 33 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 33 27, endpointJoint24Q (endpointMeanCornerK 33 27 h) (endpointMeanCornerA 33 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 33 27, endpointRunWeightQ (endpointMeanCutoff 33 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 33 27) = (97885819/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 33 27 h = (logRoundedQ ((endpointMeanCutoff 33 27:ℚ)/200)).2+(97885819/250000000000000:ℚ)+((endpointMeanRuns 33 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 33 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 33 27) r*endpointJoint24Q (endpointMeanCornerK 33 27 h) (endpointMeanCornerA 33 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 33 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 33 27 h≤endpointMeanCorner 33 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 33 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint33_27

namespace EndpointAnalyticJoint34_12
private noncomputable def weights : IntegerLookupTree := (.branch 1468 (.leaf (147749012400000:ℤ)) (.branch 2700 (.leaf (31462639900000:ℤ)) (.leaf (3202333700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (1882636597945855:ℤ)) (.branch 146 (.leaf (2141860082393048:ℤ)) (.leaf (2571587438042267:ℤ)))), (.branch 125 (.leaf (1892563762867372:ℤ)) (.branch 146 (.leaf (2158537402848972:ℤ)) (.leaf (2603085517655277:ℤ)))), (.branch 125 (.leaf (1889779874949258:ℤ)) (.branch 146 (.leaf (2156058667152062:ℤ)) (.leaf (2605925210675267:ℤ)))), (.branch 125 (.leaf (1900153037280044:ℤ)) (.branch 146 (.leaf (2173661417699111:ℤ)) (.leaf (2639830253708628:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 34 12) 8000 (endpointMeanRuns 34 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 34 12, EndpointRunConditions (endpointMeanCutoff 34 12) (endpointMeanBox 34 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 34 12 h) (endpointMeanCornerA 34 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 12, endpointJoint24Q (endpointMeanCornerK 34 12 h) (endpointMeanCornerA 34 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 34 12, endpointRunWeightQ (endpointMeanCutoff 34 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 34 12) = (408039743/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 34 12 h = (logRoundedQ ((endpointMeanCutoff 34 12:ℚ)/200)).2+(408039743/1000000000000000:ℚ)+((endpointMeanRuns 34 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 34 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 34 12) r*endpointJoint24Q (endpointMeanCornerK 34 12 h) (endpointMeanCornerA 34 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 34 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 34 12 h≤endpointMeanCorner 34 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 34 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint34_12

namespace EndpointAnalyticJoint34_13
private noncomputable def weights : IntegerLookupTree := (.branch 1468 (.branch 1072 (.leaf (77569252900000:ℤ)) (.leaf (33619982700000:ℤ))) (.branch 2700 (.leaf (31318381100000:ℤ)) (.leaf (3190902200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 146 (.branch 125 (.leaf (1892563762867372:ℤ)) (.leaf (2158537402848972:ℤ))) (.branch 163 (.leaf (2603085517655277:ℤ)) (.leaf (3126154855754921:ℤ)))), (.branch 146 (.branch 125 (.leaf (1906874777029829:ℤ)) (.leaf (2182652609582524:ℤ))) (.branch 163 (.leaf (2648876920502086:ℤ)) (.leaf (3205245460088490:ℤ)))), (.branch 146 (.branch 125 (.leaf (1900153037280044:ℤ)) (.leaf (2173661417699111:ℤ))) (.branch 163 (.leaf (2639830253708628:ℤ)) (.leaf (3207881640052310:ℤ)))), (.branch 146 (.branch 125 (.leaf (1915110912630874:ℤ)) (.leaf (2199126401938583:ℤ))) (.branch 163 (.leaf (2689166048150367:ℤ)) (.leaf (3295575644622963:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 34 13) 8000 (endpointMeanRuns 34 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 34 13, EndpointRunConditions (endpointMeanCutoff 34 13) (endpointMeanBox 34 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 34 13 h) (endpointMeanCornerA 34 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 13, endpointJoint24Q (endpointMeanCornerK 34 13 h) (endpointMeanCornerA 34 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 34 13, endpointRunWeightQ (endpointMeanCutoff 34 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 34 13) = (40700109/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 34 13 h = (logRoundedQ ((endpointMeanCutoff 34 13:ℚ)/200)).2+(40700109/100000000000000:ℚ)+((endpointMeanRuns 34 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 34 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 34 13) r*endpointJoint24Q (endpointMeanCornerK 34 13 h) (endpointMeanCornerA 34 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 34 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 34 13 h≤endpointMeanCorner 34 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 34 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint34_13

namespace EndpointAnalyticJoint34_14
private noncomputable def weights : IntegerLookupTree := (.branch 1570 (.branch 1107 (.leaf (80618975400000:ℤ)) (.leaf (35389610500000:ℤ))) (.branch 2700 (.leaf (23070878300000:ℤ)) (.leaf (3175818900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 143 (.branch 125 (.leaf (1906874777029829:ℤ)) (.leaf (2182652609582524:ℤ))) (.branch 161 (.leaf (2570610126178080:ℤ)) (.leaf (3127308018486164:ℤ)))), (.branch 143 (.branch 125 (.leaf (1921294006899667:ℤ)) (.leaf (2207037231705890:ℤ))) (.branch 161 (.leaf (2613030478427212:ℤ)) (.leaf (3203082011278930:ℤ)))), (.branch 143 (.branch 125 (.leaf (1915110912630874:ℤ)) (.leaf (2199126401938583:ℤ))) (.branch 161 (.leaf (2605891616447116:ℤ)) (.leaf (3208939026004567:ℤ)))), (.branch 143 (.branch 125 (.leaf (1930186535358165:ℤ)) (.leaf (2224889714803221:ℤ))) (.branch 161 (.leaf (2651474634955976:ℤ)) (.leaf (3292745829651980:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 34 14) 8000 (endpointMeanRuns 34 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 34 14, EndpointRunConditions (endpointMeanCutoff 34 14) (endpointMeanBox 34 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 34 14 h) (endpointMeanCornerA 34 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 14, endpointJoint24Q (endpointMeanCornerK 34 14 h) (endpointMeanCornerA 34 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 34 14, endpointRunWeightQ (endpointMeanCutoff 34 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 34 14) = (202815319/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 34 14 h = (logRoundedQ ((endpointMeanCutoff 34 14:ℚ)/200)).2+(202815319/500000000000000:ℚ)+((endpointMeanRuns 34 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 34 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 34 14) r*endpointJoint24Q (endpointMeanCornerK 34 14 h) (endpointMeanCornerA 34 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 34 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 34 14 h≤endpointMeanCorner 34 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 34 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint34_14

namespace EndpointAnalyticJoint34_15
private noncomputable def weights : IntegerLookupTree := (.branch 1570 (.branch 1107 (.leaf (77251185900000:ℤ)) (.leaf (35134326600000:ℤ))) (.branch 2700 (.leaf (22935232900000:ℤ)) (.leaf (3160913000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 143 (.branch 125 (.leaf (1921294006899667:ℤ)) (.leaf (2207037231705890:ℤ))) (.branch 161 (.leaf (2613030478427212:ℤ)) (.leaf (3203082011278930:ℤ)))), (.branch 143 (.branch 125 (.leaf (1935822270772439:ℤ)) (.leaf (2231694279131148:ℤ))) (.branch 161 (.leaf (2656150853704576:ℤ)) (.leaf (3280691991428814:ℤ)))), (.branch 143 (.branch 125 (.leaf (1930186535358165:ℤ)) (.leaf (2224889714803221:ℤ))) (.branch 161 (.leaf (2651474634955976:ℤ)) (.leaf (3292745829651980:ℤ)))), (.branch 143 (.branch 125 (.leaf (1945380832361246:ℤ)) (.leaf (2250954851287083:ℤ))) (.branch 161 (.leaf (2697855004959908:ℤ)) (.leaf (3378741387987679:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 34 15) 8000 (endpointMeanRuns 34 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 34 15, EndpointRunConditions (endpointMeanCutoff 34 15) (endpointMeanBox 34 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 34 15 h) (endpointMeanCornerA 34 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 15, endpointJoint24Q (endpointMeanCornerK 34 15 h) (endpointMeanCornerA 34 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 34 15, endpointRunWeightQ (endpointMeanCutoff 34 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 34 15) = (404276309/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 34 15 h = (logRoundedQ ((endpointMeanCutoff 34 15:ℚ)/200)).2+(404276309/1000000000000000:ℚ)+((endpointMeanRuns 34 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 34 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 34 15) r*endpointJoint24Q (endpointMeanCornerK 34 15 h) (endpointMeanCornerA 34 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 34 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 34 15 h≤endpointMeanCorner 34 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 34 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint34_15

namespace EndpointAnalyticJoint34_16
private noncomputable def weights : IntegerLookupTree := (.branch 1570 (.branch 965 (.leaf (48371597600000:ℤ)) (.leaf (59592228800000:ℤ))) (.branch 2700 (.leaf (22784515300000:ℤ)) (.leaf (3144350800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 143 (.branch 125 (.leaf (1935822270772439:ℤ)) (.leaf (2231694279131148:ℤ))) (.branch 170 (.leaf (2656150853704576:ℤ)) (.leaf (3725001297396365:ℤ)))), (.branch 143 (.branch 125 (.leaf (1950460393131422:ℤ)) (.leaf (2256626795397165:ℤ))) (.branch 170 (.leaf (2699982803829388:ℤ)) (.leaf (3834863726902070:ℤ)))), (.branch 143 (.branch 125 (.leaf (1945380832361246:ℤ)) (.leaf (2250954851287083:ℤ))) (.branch 170 (.leaf (2697855004959908:ℤ)) (.leaf (3884296361765590:ℤ)))), (.branch 143 (.branch 125 (.leaf (1960694737835940:ℤ)) (.leaf (2277325347328950:ℤ))) (.branch 170 (.leaf (2745046673964536:ℤ)) (.leaf (4009336300109850:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 34 16) 8000 (endpointMeanRuns 34 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 34 16, EndpointRunConditions (endpointMeanCutoff 34 16) (endpointMeanBox 34 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 34 16 h) (endpointMeanCornerA 34 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 16, endpointJoint24Q (endpointMeanCornerK 34 16 h) (endpointMeanCornerA 34 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 34 16, endpointRunWeightQ (endpointMeanCutoff 34 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 34 16) = (80554299/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 34 16 h = (logRoundedQ ((endpointMeanCutoff 34 16:ℚ)/200)).2+(80554299/200000000000000:ℚ)+((endpointMeanRuns 34 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 34 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 34 16) r*endpointJoint24Q (endpointMeanCornerK 34 16 h) (endpointMeanCornerA 34 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 34 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 34 16 h≤endpointMeanCorner 34 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 34 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint34_16

namespace EndpointAnalyticJoint34_17
private noncomputable def weights : IntegerLookupTree := (.branch 1570 (.branch 979 (.leaf (48306263100000:ℤ)) (.leaf (56255100600000:ℤ))) (.branch 2700 (.leaf (22652178400000:ℤ)) (.leaf (3129808500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 143 (.branch 125 (.leaf (1950460393131422:ℤ)) (.leaf (2256626795397165:ℤ))) (.branch 169 (.leaf (2699982803829388:ℤ)) (.leaf (3775212514975331:ℤ)))), (.branch 143 (.branch 125 (.leaf (1965209204694383:ℤ)) (.leaf (2281837858045264:ℤ))) (.branch 169 (.leaf (2744538071249625:ℤ)) (.leaf (3884115566538733:ℤ)))), (.branch 143 (.branch 125 (.leaf (1960694737835940:ℤ)) (.leaf (2277325347328950:ℤ))) (.branch 169 (.leaf (2745046673964536:ℤ)) (.leaf (3939964792518015:ℤ)))), (.branch 143 (.branch 125 (.leaf (1976129193331991:ℤ)) (.leaf (2304004780292006:ℤ))) (.branch 169 (.leaf (2793063833449321:ℤ)) (.leaf (4063818581782061:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 34 17) 8000 (endpointMeanRuns 34 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 34 17, EndpointRunConditions (endpointMeanCutoff 34 17) (endpointMeanBox 34 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 34 17 h) (endpointMeanCornerA 34 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 17, endpointJoint24Q (endpointMeanCornerK 34 17 h) (endpointMeanCornerA 34 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 34 17, endpointRunWeightQ (endpointMeanCutoff 34 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 34 17) = (2007251/5000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 34 17 h = (logRoundedQ ((endpointMeanCutoff 34 17:ℚ)/200)).2+(2007251/5000000000000:ℚ)+((endpointMeanRuns 34 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 34 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 34 17) r*endpointJoint24Q (endpointMeanCornerK 34 17 h) (endpointMeanCornerA 34 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 34 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 34 17 h≤endpointMeanCorner 34 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 34 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint34_17

namespace EndpointAnalyticJoint34_18
private noncomputable def weights : IntegerLookupTree := (.branch 1570 (.branch 1185 (.leaf (80073932100000:ℤ)) (.leaf (24710663800000:ℤ))) (.branch 2700 (.leaf (22521343200000:ℤ)) (.leaf (3115431200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 143 (.branch 125 (.leaf (1965209204694383:ℤ)) (.leaf (2281837858045264:ℤ))) (.branch 157 (.leaf (2744538071249625:ℤ)) (.leaf (3257190057697101:ℤ)))), (.branch 143 (.branch 125 (.leaf (1980069542460738:ℤ)) (.leaf (2307330578999085:ℤ))) (.branch 157 (.leaf (2789828592187803:ℤ)) (.leaf (3329617296565505:ℤ)))), (.branch 143 (.branch 125 (.leaf (1976129193331991:ℤ)) (.leaf (2304004780292006:ℤ))) (.branch 157 (.leaf (2793063833449321:ℤ)) (.leaf (3351630566497565:ℤ)))), (.branch 143 (.branch 125 (.leaf (1991685147810955:ℤ)) (.leaf (2330996769449134:ℤ))) (.branch 157 (.leaf (2841920923135241:ℤ)) (.leaf (3431602490800556:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 34 18) 8000 (endpointMeanRuns 34 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 34 18, EndpointRunConditions (endpointMeanCutoff 34 18) (endpointMeanBox 34 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 34 18 h) (endpointMeanCornerA 34 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 18, endpointJoint24Q (endpointMeanCornerK 34 18 h) (endpointMeanCornerA 34 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 34 18, endpointRunWeightQ (endpointMeanCutoff 34 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 34 18) = (200071949/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 34 18 h = (logRoundedQ ((endpointMeanCutoff 34 18:ℚ)/200)).2+(200071949/500000000000000:ℚ)+((endpointMeanRuns 34 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 34 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 34 18) r*endpointJoint24Q (endpointMeanCornerK 34 18 h) (endpointMeanCornerA 34 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 34 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 34 18 h≤endpointMeanCorner 34 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 34 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint34_18

namespace EndpointAnalyticJoint34_19
private noncomputable def weights : IntegerLookupTree := (.branch 1468 (.branch 951 (.leaf (38687955700000:ℤ)) (.leaf (52549954400000:ℤ))) (.branch 2700 (.leaf (30186587100000:ℤ)) (.leaf (3101215200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 146 (.branch 125 (.leaf (1980069542460738:ℤ)) (.leaf (2307330578999085:ℤ))) (.branch 171 (.leaf (2890203990696901:ℤ)) (.leaf (4135119265467491:ℤ)))), (.branch 146 (.branch 125 (.leaf (1995042249759053:ℤ)) (.leaf (2333108104948730:ℤ))) (.branch 171 (.leaf (2941046152565887:ℤ)) (.leaf (4259822737065303:ℤ)))), (.branch 146 (.branch 125 (.leaf (1991685147810955:ℤ)) (.leaf (2330996769449134:ℤ))) (.branch 171 (.leaf (2950025078111483:ℤ)) (.leaf (4355047898955249:ℤ)))), (.branch 146 (.branch 125 (.leaf (2007363557704565:ℤ)) (.leaf (2358304976473906:ℤ))) (.branch 171 (.leaf (3005158104429068:ℤ)) (.leaf (4498636384155868:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 34 19) 8000 (endpointMeanRuns 34 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 34 19, EndpointRunConditions (endpointMeanCutoff 34 19) (endpointMeanBox 34 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 34 19 h) (endpointMeanCornerA 34 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 19, endpointJoint24Q (endpointMeanCornerK 34 19 h) (endpointMeanCornerA 34 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 34 19, endpointRunWeightQ (endpointMeanCutoff 34 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 34 19) = (398852253/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 34 19 h = (logRoundedQ ((endpointMeanCutoff 34 19:ℚ)/200)).2+(398852253/1000000000000000:ℚ)+((endpointMeanRuns 34 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 34 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 34 19) r*endpointJoint24Q (endpointMeanCornerK 34 19 h) (endpointMeanCornerA 34 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 34 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 34 19 h≤endpointMeanCorner 34 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 34 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint34_19

namespace EndpointAnalyticJoint34_20
private noncomputable def weights : IntegerLookupTree := (.branch 1570 (.branch 1274 (.leaf (87036233100000:ℤ)) (.leaf (15935547700000:ℤ))) (.branch 2700 (.leaf (22264044300000:ℤ)) (.leaf (3087157000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 143 (.branch 125 (.leaf (1995042249759053:ℤ)) (.leaf (2333108104948730:ℤ))) (.branch 153 (.leaf (2835866499838640:ℤ)) (.leaf (3219481913435901:ℤ)))), (.branch 143 (.branch 125 (.leaf (2010128176294888:ℤ)) (.leaf (2359173617739155:ℤ))) (.branch 153 (.leaf (2882664127619528:ℤ)) (.leaf (3285212943013242:ℤ)))), (.branch 143 (.branch 125 (.leaf (2007363557704565:ℤ)) (.leaf (2358304976473906:ℤ))) (.branch 153 (.leaf (2891632635327097:ℤ)) (.leaf (3309281669042467:ℤ)))), (.branch 143 (.branch 125 (.leaf (2023165386973498:ℤ)) (.leaf (2385933105937302:ℤ))) (.branch 153 (.leaf (2942213919331782:ℤ)) (.leaf (3381494274310684:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 34 20) 8000 (endpointMeanRuns 34 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 34 20, EndpointRunConditions (endpointMeanCutoff 34 20) (endpointMeanBox 34 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 34 20 h) (endpointMeanCornerA 34 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 20, endpointJoint24Q (endpointMeanCornerK 34 20 h) (endpointMeanCornerA 34 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 34 20, endpointRunWeightQ (endpointMeanCutoff 34 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 34 20) = (397574941/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 34 20 h = (logRoundedQ ((endpointMeanCutoff 34 20:ℚ)/200)).2+(397574941/1000000000000000:ℚ)+((endpointMeanRuns 34 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 34 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 34 20) r*endpointJoint24Q (endpointMeanCornerK 34 20 h) (endpointMeanCornerA 34 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 34 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 34 20 h≤endpointMeanCorner 34 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 34 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint34_20

namespace EndpointAnalyticJoint34_21
private noncomputable def weights : IntegerLookupTree := (.branch 1570 (.branch 1185 (.leaf (70889353100000:ℤ)) (.leaf (24205602500000:ℤ))) (.branch 2700 (.leaf (22137516500000:ℤ)) (.leaf (3073253000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 143 (.branch 125 (.leaf (2010128176294888:ℤ)) (.leaf (2359173617739155:ℤ))) (.branch 157 (.leaf (2882664127619528:ℤ)) (.leaf (3479339085876185:ℤ)))), (.branch 143 (.branch 125 (.leaf (2025328178199040:ℤ)) (.leaf (2385530334762932:ℤ))) (.branch 157 (.leaf (2930234012474589:ℤ)) (.leaf (3556706055138981:ℤ)))), (.branch 143 (.branch 125 (.leaf (2023165386973498:ℤ)) (.leaf (2385933105937302:ℤ))) (.branch 157 (.leaf (2942213919331782:ℤ)) (.leaf (3597316404554254:ℤ)))), (.branch 143 (.branch 125 (.leaf (2039091607166679:ℤ)) (.leaf (2413884905810278:ℤ))) (.branch 157 (.leaf (2993679985953837:ℤ)) (.leaf (3683150540951792:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 34 21) 8000 (endpointMeanRuns 34 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 34 21, EndpointRunConditions (endpointMeanCutoff 34 21) (endpointMeanBox 34 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 34 21 h) (endpointMeanCornerA 34 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 21, endpointJoint24Q (endpointMeanCornerK 34 21 h) (endpointMeanCornerA 34 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 34 21, endpointRunWeightQ (endpointMeanCutoff 34 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 34 21) = (198155823/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 34 21 h = (logRoundedQ ((endpointMeanCutoff 34 21:ℚ)/200)).2+(198155823/500000000000000:ℚ)+((endpointMeanRuns 34 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 34 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 34 21) r*endpointJoint24Q (endpointMeanCornerK 34 21 h) (endpointMeanCornerA 34 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 34 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 34 21 h≤endpointMeanCorner 34 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 34 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint34_21

namespace EndpointAnalyticJoint34_22
private noncomputable def weights : IntegerLookupTree := (.branch 1570 (.branch 1185 (.leaf (68037787800000:ℤ)) (.leaf (24040917200000:ℤ))) (.branch 2700 (.leaf (22012362200000:ℤ)) (.leaf (3059500000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 143 (.branch 125 (.leaf (2025328178199040:ℤ)) (.leaf (2385530334762932:ℤ))) (.branch 157 (.leaf (2930234012474589:ℤ)) (.leaf (3556706055138981:ℤ)))), (.branch 143 (.branch 125 (.leaf (2040643118076109:ℤ)) (.leaf (2412181509357381:ℤ))) (.branch 157 (.leaf (2978588898233312:ℤ)) (.leaf (3635793364898974:ℤ)))), (.branch 143 (.branch 125 (.leaf (2039091607166679:ℤ)) (.leaf (2413884905810278:ℤ))) (.branch 157 (.leaf (2993679985953837:ℤ)) (.leaf (3683150540951792:ℤ)))), (.branch 143 (.branch 125 (.leaf (2055143197481000:ℤ)) (.leaf (2442164167972196:ℤ))) (.branch 157 (.leaf (3046046312069651:ℤ)) (.leaf (3771032731549342:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 34 22) 8000 (endpointMeanRuns 34 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 34 22, EndpointRunConditions (endpointMeanCutoff 34 22) (endpointMeanBox 34 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 34 22 h) (endpointMeanCornerA 34 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 22, endpointJoint24Q (endpointMeanCornerK 34 22 h) (endpointMeanCornerA 34 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 34 22, endpointRunWeightQ (endpointMeanCutoff 34 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 34 22) = (24691379/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 34 22 h = (logRoundedQ ((endpointMeanCutoff 34 22:ℚ)/200)).2+(24691379/62500000000000:ℚ)+((endpointMeanRuns 34 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 34 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 34 22) r*endpointJoint24Q (endpointMeanCornerK 34 22 h) (endpointMeanCornerA 34 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 34 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 34 22 h≤endpointMeanCorner 34 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 34 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint34_22

namespace EndpointAnalyticJoint34_23
private noncomputable def weights : IntegerLookupTree := (.branch 1324 (.leaf (84306216500000:ℤ)) (.branch 2700 (.leaf (44506712400000:ℤ)) (.leaf (3045894600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2040643118076109:ℤ)) (.branch 151 (.leaf (2412181509357381:ℤ)) (.leaf (3322318900681631:ℤ)))), (.branch 125 (.leaf (2056073865053459:ℤ)) (.branch 151 (.leaf (2439130431206147:ℤ)) (.leaf (3387322056869393:ℤ)))), (.branch 125 (.leaf (2055143197481000:ℤ)) (.branch 151 (.leaf (2442164167972196:ℤ)) (.leaf (3421733507895447:ℤ)))), (.branch 125 (.leaf (2071321144821510:ℤ)) (.branch 151 (.leaf (2470774728725232:ℤ)) (.leaf (3493156869216339:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 34 23) 8000 (endpointMeanRuns 34 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 34 23, EndpointRunConditions (endpointMeanCutoff 34 23) (endpointMeanBox 34 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 34 23 h) (endpointMeanCornerA 34 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 23, endpointJoint24Q (endpointMeanCornerK 34 23 h) (endpointMeanCornerA 34 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 34 23, endpointRunWeightQ (endpointMeanCutoff 34 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 34 23) = (3938259/10000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 34 23 h = (logRoundedQ ((endpointMeanCutoff 34 23:ℚ)/200)).2+(3938259/10000000000000:ℚ)+((endpointMeanRuns 34 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 34 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 34 23) r*endpointJoint24Q (endpointMeanCornerK 34 23 h) (endpointMeanCornerA 34 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 34 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 34 23 h≤endpointMeanCorner 34 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 34 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint34_23

namespace EndpointAnalyticJoint34_24
private noncomputable def weights : IntegerLookupTree := (.branch 1468 (.leaf (98866896900000:ℤ)) (.branch 2700 (.leaf (29318608700000:ℤ)) (.leaf (3032433800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2056073865053459:ℤ)) (.branch 146 (.leaf (2439130431206147:ℤ)) (.leaf (3153517267331901:ℤ)))), (.branch 125 (.leaf (2071621294830549:ℤ)) (.branch 146 (.leaf (2466380426745258:ℤ)) (.leaf (3208991426207342:ℤ)))), (.branch 125 (.leaf (2071321144821510:ℤ)) (.branch 146 (.leaf (2470774728725232:ℤ)) (.leaf (3236188396574632:ℤ)))), (.branch 125 (.leaf (2087626443862127:ℤ)) (.branch 146 (.leaf (2499720469314806:ℤ)) (.leaf (3296669529891380:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 34 24) 8000 (endpointMeanRuns 34 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 34 24, EndpointRunConditions (endpointMeanCutoff 34 24) (endpointMeanBox 34 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 34 24 h) (endpointMeanCornerA 34 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 24, endpointJoint24Q (endpointMeanCornerK 34 24 h) (endpointMeanCornerA 34 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 34 24, endpointRunWeightQ (endpointMeanCutoff 34 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 34 24) = (392602871/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 34 24 h = (logRoundedQ ((endpointMeanCutoff 34 24:ℚ)/200)).2+(392602871/1000000000000000:ℚ)+((endpointMeanRuns 34 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 34 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 34 24) r*endpointJoint24Q (endpointMeanCornerK 34 24 h) (endpointMeanCornerA 34 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 34 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 34 24 h≤endpointMeanCorner 34 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 34 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint34_24

namespace EndpointAnalyticJoint34_25
private noncomputable def weights : IntegerLookupTree := (.branch 1407 (.leaf (88426711200000:ℤ)) (.branch 2700 (.leaf (34740386800000:ℤ)) (.leaf (3019114500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2071621294830549:ℤ)) (.branch 148 (.leaf (2466380426745258:ℤ)) (.leaf (3302692099037725:ℤ)))), (.branch 125 (.leaf (2087286289728606:ℤ)) (.branch 148 (.leaf (2493934859573735:ℤ)) (.leaf (3363316162645047:ℤ)))), (.branch 125 (.leaf (2087626443862127:ℤ)) (.branch 148 (.leaf (2499720469314806:ℤ)) (.leaf (3399442279509440:ℤ)))), (.branch 125 (.leaf (2104060097106756:ℤ)) (.branch 148 (.leaf (2529005316456072:ℤ)) (.leaf (3465842809179823:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 34 25) 8000 (endpointMeanRuns 34 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 34 25, EndpointRunConditions (endpointMeanCutoff 34 25) (endpointMeanBox 34 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 34 25 h) (endpointMeanCornerA 34 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 25, endpointJoint24Q (endpointMeanCornerK 34 25 h) (endpointMeanCornerA 34 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 34 25, endpointRunWeightQ (endpointMeanCutoff 34 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 34 25) = (195696349/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 34 25 h = (logRoundedQ ((endpointMeanCutoff 34 25:ℚ)/200)).2+(195696349/500000000000000:ℚ)+((endpointMeanRuns 34 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 34 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 34 25) r*endpointJoint24Q (endpointMeanCornerK 34 25 h) (endpointMeanCornerA 34 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 34 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 34 25 h≤endpointMeanCorner 34 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 34 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint34_25

namespace EndpointAnalyticJoint34_26
private noncomputable def weights : IntegerLookupTree := (.branch 1468 (.leaf (92341096100000:ℤ)) (.branch 2700 (.leaf (28984194900000:ℤ)) (.leaf (3005933800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2087286289728606:ℤ)) (.branch 146 (.leaf (2493934859573735:ℤ)) (.leaf (3265441442210572:ℤ)))), (.branch 125 (.leaf (2103069738740732:ℤ)) (.branch 146 (.leaf (2521797130868764:ℤ)) (.leaf (3322884481841327:ℤ)))), (.branch 125 (.leaf (2104060097106756:ℤ)) (.branch 146 (.leaf (2529005316456072:ℤ)) (.leaf (3358280995265172:ℤ)))), (.branch 125 (.leaf (2120623114950957:ℤ)) (.branch 146 (.leaf (2558633242866651:ℤ)) (.leaf (3421043917474743:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 34 26) 8000 (endpointMeanRuns 34 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 34 26, EndpointRunConditions (endpointMeanCutoff 34 26) (endpointMeanBox 34 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 34 26 h) (endpointMeanCornerA 34 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 26, endpointJoint24Q (endpointMeanCornerK 34 26 h) (endpointMeanCornerA 34 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 34 26, endpointRunWeightQ (endpointMeanCutoff 34 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 34 26) = (78039023/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 34 26 h = (logRoundedQ ((endpointMeanCutoff 34 26:ℚ)/200)).2+(78039023/200000000000000:ℚ)+((endpointMeanRuns 34 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 34 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 34 26) r*endpointJoint24Q (endpointMeanCornerK 34 26 h) (endpointMeanCornerA 34 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 34 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 34 26 h≤endpointMeanCorner 34 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 34 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint34_26

namespace EndpointAnalyticJoint34_27
private noncomputable def weights : IntegerLookupTree := (.branch 1468 (.leaf (89233342400000:ℤ)) (.leaf (64844105500000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 146 (.leaf (2103069738740732:ℤ)) (.leaf (3322884481841327:ℤ))), (.branch 146 (.leaf (2118972537582318:ℤ)) (.leaf (3381338013578718:ℤ))), (.branch 146 (.leaf (2120623114950957:ℤ)) (.leaf (3421043917474743:ℤ))), (.branch 146 (.leaf (2137316515744048:ℤ)) (.leaf (3484979816099879:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 34 27) 8000 (endpointMeanRuns 34 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 34 27, EndpointRunConditions (endpointMeanCutoff 34 27) (endpointMeanBox 34 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 34 27 h) (endpointMeanCornerA 34 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 34 27, endpointJoint24Q (endpointMeanCornerK 34 27 h) (endpointMeanCornerA 34 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 34 27, endpointRunWeightQ (endpointMeanCutoff 34 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 34 27) = (389009863/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 34 27 h = (logRoundedQ ((endpointMeanCutoff 34 27:ℚ)/200)).2+(389009863/1000000000000000:ℚ)+((endpointMeanRuns 34 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 34 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 34 27) r*endpointJoint24Q (endpointMeanCornerK 34 27 h) (endpointMeanCornerA 34 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 34 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 34 27 h≤endpointMeanCorner 34 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 34 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint34_27

namespace EndpointAnalyticJoint35_12
private noncomputable def weights : IntegerLookupTree := (.branch 961 (.leaf (52975225300000:ℤ)) (.branch 1579 (.leaf (63278760200000:ℤ)) (.leaf (53212856000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.leaf (1900123937290339:ℤ)) (.branch 169 (.leaf (2535837869810626:ℤ)) (.leaf (3480953356206594:ℤ)))), (.branch 142 (.leaf (1900153037280044:ℤ)) (.branch 169 (.leaf (2535921900259475:ℤ)) (.leaf (3481163792191352:ℤ)))), (.branch 142 (.leaf (1908207366145135:ℤ)) (.branch 169 (.leaf (2570577514294170:ℤ)) (.leaf (3621290677489027:ℤ)))), (.branch 142 (.leaf (1908237807169768:ℤ)) (.branch 169 (.leaf (2570667951771317:ℤ)) (.leaf (3621531105707710:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 35 12) 8000 (endpointMeanRuns 35 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 35 12, EndpointRunConditions (endpointMeanCutoff 35 12) (endpointMeanBox 35 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 35 12 h) (endpointMeanCornerA 35 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 12, endpointJoint24Q (endpointMeanCornerK 35 12 h) (endpointMeanCornerA 35 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 35 12, endpointRunWeightQ (endpointMeanCutoff 35 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 35 12) = (404782317/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 35 12 h = (logRoundedQ ((endpointMeanCutoff 35 12:ℚ)/200)).2+(404782317/1000000000000000:ℚ)+((endpointMeanRuns 35 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 35 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 35 12) r*endpointJoint24Q (endpointMeanCornerK 35 12 h) (endpointMeanCornerA 35 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 35 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 35 12 h≤endpointMeanCorner 35 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 35 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint35_12

namespace EndpointAnalyticJoint35_13
private noncomputable def weights : IntegerLookupTree := (.branch 1124 (.leaf (81687391800000:ℤ)) (.branch 2652 (.leaf (81557758900000:ℤ)) (.leaf (3573174000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (1900153037280044:ℤ)) (.branch 159 (.leaf (2173661417699111:ℤ)) (.leaf (3051062249950177:ℤ)))), (.branch 125 (.leaf (1915110912630874:ℤ)) (.branch 159 (.leaf (2199126401938583:ℤ)) (.leaf (3127215121187837:ℤ)))), (.branch 125 (.leaf (1908237807169768:ℤ)) (.branch 159 (.leaf (2190140010425350:ℤ)) (.leaf (3130814721175037:ℤ)))), (.branch 125 (.leaf (1923887560405261:ℤ)) (.branch 159 (.leaf (2217085702444840:ℤ)) (.leaf (3215333897522555:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 35 13) 8000 (endpointMeanRuns 35 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 35 13, EndpointRunConditions (endpointMeanCutoff 35 13) (endpointMeanBox 35 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 35 13 h) (endpointMeanCornerA 35 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 13, endpointJoint24Q (endpointMeanCornerK 35 13 h) (endpointMeanCornerA 35 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 35 13, endpointRunWeightQ (endpointMeanCutoff 35 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 35 13) = (404108133/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 35 13 h = (logRoundedQ ((endpointMeanCutoff 35 13:ℚ)/200)).2+(404108133/1000000000000000:ℚ)+((endpointMeanRuns 35 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 35 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 35 13) r*endpointJoint24Q (endpointMeanCornerK 35 13 h) (endpointMeanCornerA 35 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 35 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 35 13 h≤endpointMeanCorner 35 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 35 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint35_13

namespace EndpointAnalyticJoint35_14
private noncomputable def weights : IntegerLookupTree := (.branch 1579 (.branch 961 (.leaf (48904384100000:ℤ)) (.leaf (62555044100000:ℤ))) (.branch 2652 (.leaf (22052771700000:ℤ)) (.leaf (3556427100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 125 (.leaf (1915110912630874:ℤ)) (.leaf (2199126401938583:ℤ))) (.branch 169 (.leaf (2579313249629102:ℤ)) (.leaf (3590595056026619:ℤ)))), (.branch 142 (.branch 125 (.leaf (1930186535358165:ℤ)) (.leaf (2224889714803221:ℤ))) (.branch 169 (.leaf (2623447054513589:ℤ)) (.leaf (3703466319304450:ℤ)))), (.branch 142 (.branch 125 (.leaf (1923887560405261:ℤ)) (.leaf (2217085702444840:ℤ))) (.branch 169 (.leaf (2617392308359505:ℤ)) (.leaf (3746750618231323:ℤ)))), (.branch 142 (.branch 125 (.leaf (1939665659686201:ℤ)) (.leaf (2244362912228014:ℤ))) (.branch 169 (.leaf (2664965924960868:ℤ)) (.leaf (3876299770859900:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 35 14) 8000 (endpointMeanRuns 35 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 35 14, EndpointRunConditions (endpointMeanCutoff 35 14) (endpointMeanBox 35 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 35 14 h) (endpointMeanCornerA 35 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 14, endpointJoint24Q (endpointMeanCornerK 35 14 h) (endpointMeanCornerA 35 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 35 14, endpointRunWeightQ (endpointMeanCutoff 35 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 35 14) = (80554299/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 35 14 h = (logRoundedQ ((endpointMeanCutoff 35 14:ℚ)/200)).2+(80554299/200000000000000:ℚ)+((endpointMeanRuns 35 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 35 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 35 14) r*endpointJoint24Q (endpointMeanCornerK 35 14 h) (endpointMeanCornerA 35 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 35 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 35 14 h≤endpointMeanCorner 35 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 35 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint35_14

namespace EndpointAnalyticJoint35_15
private noncomputable def weights : IntegerLookupTree := (.branch 1579 (.branch 990 (.leaf (51540039500000:ℤ)) (.leaf (56015904100000:ℤ))) (.branch 2652 (.leaf (21924861200000:ℤ)) (.leaf (3539872600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 125 (.leaf (1930186535358165:ℤ)) (.leaf (2224889714803221:ℤ))) (.branch 167 (.leaf (2623447054513589:ℤ)) (.leaf (3590289017293866:ℤ)))), (.branch 142 (.branch 125 (.leaf (1945380832361246:ℤ)) (.leaf (2250954851287083:ℤ))) (.branch 167 (.leaf (2668336018832039:ℤ)) (.leaf (3697960873651518:ℤ)))), (.branch 142 (.branch 125 (.leaf (1939665659686201:ℤ)) (.leaf (2244362912228014:ℤ))) (.branch 167 (.leaf (2664965924960868:ℤ)) (.leaf (3743158713122342:ℤ)))), (.branch 142 (.branch 125 (.leaf (1955573157598354:ℤ)) (.leaf (2271975718498380:ℤ))) (.branch 167 (.leaf (2713404237691003:ℤ)) (.leaf (3866147317766577:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 35 15) 8000 (endpointMeanRuns 35 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 35 15, EndpointRunConditions (endpointMeanCutoff 35 15) (endpointMeanBox 35 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 35 15 h) (endpointMeanCornerA 35 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 15, endpointJoint24Q (endpointMeanCornerK 35 15 h) (endpointMeanCornerA 35 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 35 15, endpointRunWeightQ (endpointMeanCutoff 35 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 35 15) = (2007251/5000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 35 15 h = (logRoundedQ ((endpointMeanCutoff 35 15:ℚ)/200)).2+(2007251/5000000000000:ℚ)+((endpointMeanRuns 35 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 35 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 35 15) r*endpointJoint24Q (endpointMeanCornerK 35 15 h) (endpointMeanCornerA 35 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 35 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 35 15 h≤endpointMeanCorner 35 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 35 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint35_15

namespace EndpointAnalyticJoint35_16
private noncomputable def weights : IntegerLookupTree := (.branch 1579 (.branch 1206 (.leaf (85286379700000:ℤ)) (.leaf (23553908700000:ℤ))) (.branch 2652 (.leaf (21798402300000:ℤ)) (.leaf (3523505800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 125 (.leaf (1945380832361246:ℤ)) (.leaf (2250954851287083:ℤ))) (.branch 155 (.leaf (2668336018832039:ℤ)) (.leaf (3114132627933861:ℤ)))), (.branch 142 (.branch 125 (.leaf (1960694737835940:ℤ)) (.leaf (2277325347328950:ℤ))) (.branch 155 (.leaf (2713993063876224:ℤ)) (.leaf (3185184069015395:ℤ)))), (.branch 142 (.branch 125 (.leaf (1955573157598354:ℤ)) (.leaf (2271975718498380:ℤ))) (.branch 155 (.leaf (2713404237691003:ℤ)) (.leaf (3199732350542370:ℤ)))), (.branch 142 (.branch 125 (.leaf (1971611115359896:ℤ)) (.leaf (2299928250160740:ℤ))) (.branch 155 (.leaf (2762722963231741:ℤ)) (.leaf (3278288094432022:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 35 16) 8000 (endpointMeanRuns 35 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 35 16, EndpointRunConditions (endpointMeanCutoff 35 16) (endpointMeanBox 35 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 35 16 h) (endpointMeanCornerA 35 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 16, endpointJoint24Q (endpointMeanCornerK 35 16 h) (endpointMeanCornerA 35 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 35 16, endpointRunWeightQ (endpointMeanCutoff 35 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 35 16) = (200071949/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 35 16 h = (logRoundedQ ((endpointMeanCutoff 35 16:ℚ)/200)).2+(200071949/500000000000000:ℚ)+((endpointMeanRuns 35 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 35 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 35 16) r*endpointJoint24Q (endpointMeanCornerK 35 16 h) (endpointMeanCornerA 35 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 35 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 35 16 h≤endpointMeanCorner 35 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 35 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint35_16

namespace EndpointAnalyticJoint35_17
private noncomputable def weights : IntegerLookupTree := (.branch 1579 (.branch 1206 (.leaf (81578172100000:ℤ)) (.leaf (23372994900000:ℤ))) (.branch 2652 (.leaf (21657830500000:ℤ)) (.leaf (3505312600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 125 (.leaf (1960694737835940:ℤ)) (.leaf (2277325347328950:ℤ))) (.branch 155 (.leaf (2713993063876224:ℤ)) (.leaf (3185184069015395:ℤ)))), (.branch 142 (.branch 125 (.leaf (1976129193331991:ℤ)) (.leaf (2304004780292006:ℤ))) (.branch 155 (.leaf (2760431332030039:ℤ)) (.leaf (3257856605882795:ℤ)))), (.branch 142 (.branch 125 (.leaf (1971611115359896:ℤ)) (.leaf (2299928250160740:ℤ))) (.branch 155 (.leaf (2762722963231741:ℤ)) (.leaf (3278288094432022:ℤ)))), (.branch 142 (.branch 125 (.leaf (1987780602892213:ℤ)) (.leaf (2328224686918552:ℤ))) (.branch 155 (.leaf (2812938103930670:ℤ)) (.leaf (3358772438661328:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 35 17) 8000 (endpointMeanRuns 35 17) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 35 17, EndpointRunConditions (endpointMeanCutoff 35 17) (endpointMeanBox 35 17).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 17, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 35 17 h) (endpointMeanCornerA 35 17 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 17, endpointJoint24Q (endpointMeanCornerK 35 17 h) (endpointMeanCornerA 35 17 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 35 17, endpointRunWeightQ (endpointMeanCutoff 35 17) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 35 17) = (99672953/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 35 17 h = (logRoundedQ ((endpointMeanCutoff 35 17:ℚ)/200)).2+(99672953/250000000000000:ℚ)+((endpointMeanRuns 35 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 35 17).map (fun r => endpointRunWeightQ (endpointMeanCutoff 35 17) r*endpointJoint24Q (endpointMeanCornerK 35 17 h) (endpointMeanCornerA 35 17 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 35 17).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 35 17 h≤endpointMeanCorner 35 17 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 35 17 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint35_17

namespace EndpointAnalyticJoint35_18
private noncomputable def weights : IntegerLookupTree := (.branch 1353 (.branch 1087 (.leaf (59739236200000:ℤ)) (.leaf (22135230000000:ℤ))) (.branch 2009 (.leaf (26279736500000:ℤ)) (.leaf (17812570200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 149 (.branch 133 (.leaf (1976129193331991:ℤ)) (.leaf (2498287216946026:ℤ))) (.branch 161 (.leaf (3006889389732586:ℤ)) (.leaf (3557528913572030:ℤ)))), (.branch 149 (.branch 133 (.leaf (1991685147810955:ℤ)) (.leaf (2533312931358290:ℤ))) (.branch 161 (.leaf (3066934968356109:ℤ)) (.leaf (3650439724501634:ℤ)))), (.branch 149 (.branch 133 (.leaf (1987780602892213:ℤ)) (.leaf (2532869281391668:ℤ))) (.branch 161 (.leaf (3080853125474427:ℤ)) (.leaf (3698108314408528:ℤ)))), (.branch 149 (.branch 133 (.leaf (2004082698891295:ℤ)) (.leaf (2570342164757229:ℤ))) (.branch 161 (.leaf (3146620857512532:ℤ)) (.leaf (3802869624217120:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 35 18) 8000 (endpointMeanRuns 35 18) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 35 18, EndpointRunConditions (endpointMeanCutoff 35 18) (endpointMeanBox 35 18).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 18, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 35 18 h) (endpointMeanCornerA 35 18 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 18, endpointJoint24Q (endpointMeanCornerK 35 18 h) (endpointMeanCornerA 35 18 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 35 18, endpointRunWeightQ (endpointMeanCutoff 35 18) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 35 18) = (397416269/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 35 18 h = (logRoundedQ ((endpointMeanCutoff 35 18:ℚ)/200)).2+(397416269/1000000000000000:ℚ)+((endpointMeanRuns 35 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 35 18).map (fun r => endpointRunWeightQ (endpointMeanCutoff 35 18) r*endpointJoint24Q (endpointMeanCornerK 35 18 h) (endpointMeanCornerA 35 18 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 35 18).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 35 18 h≤endpointMeanCorner 35 18 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 35 18 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint35_18

namespace EndpointAnalyticJoint35_19
private noncomputable def weights : IntegerLookupTree := (.branch 1579 (.branch 1206 (.leaf (75334817200000:ℤ)) (.leaf (23056899400000:ℤ))) (.branch 2652 (.leaf (21412221200000:ℤ)) (.leaf (3473525000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.branch 125 (.leaf (1991685147810955:ℤ)) (.leaf (2330996769449134:ℤ))) (.branch 155 (.leaf (2807664190552506:ℤ)) (.leaf (3332187225140504:ℤ)))), (.branch 142 (.branch 125 (.leaf (2007363557704565:ℤ)) (.leaf (2358304976473906:ℤ))) (.branch 155 (.leaf (2855705235425527:ℤ)) (.leaf (3408213757272112:ℤ)))), (.branch 142 (.branch 125 (.leaf (2004082698891295:ℤ)) (.leaf (2356869259898932:ℤ))) (.branch 155 (.leaf (2864065952993398:ℤ)) (.leaf (3441232731763775:ℤ)))), (.branch 142 (.branch 125 (.leaf (2020518490899671:ℤ)) (.leaf (2385866252285322:ℤ))) (.branch 155 (.leaf (2916123099770191:ℤ)) (.leaf (3525717484713596:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 35 19) 8000 (endpointMeanRuns 35 19) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 35 19, EndpointRunConditions (endpointMeanCutoff 35 19) (endpointMeanBox 35 19).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 19, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 35 19 h) (endpointMeanCornerA 35 19 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 19, endpointJoint24Q (endpointMeanCornerK 35 19 h) (endpointMeanCornerA 35 19 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 35 19, endpointRunWeightQ (endpointMeanCutoff 35 19) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 35 19) = (24759669/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 35 19 h = (logRoundedQ ((endpointMeanCutoff 35 19:ℚ)/200)).2+(24759669/62500000000000:ℚ)+((endpointMeanRuns 35 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 35 19).map (fun r => endpointRunWeightQ (endpointMeanCutoff 35 19) r*endpointJoint24Q (endpointMeanCornerK 35 19 h) (endpointMeanCornerA 35 19 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 35 19).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 35 19 h≤endpointMeanCorner 35 19 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 35 19 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint35_19

namespace EndpointAnalyticJoint35_20
private noncomputable def weights : IntegerLookupTree := (.branch 1353 (.branch 1087 (.leaf (54499096100000:ℤ)) (.leaf (21813210600000:ℤ))) (.branch 2009 (.leaf (25955201300000:ℤ)) (.leaf (17634136700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 149 (.branch 133 (.leaf (2007363557704565:ℤ)) (.leaf (2568829702468027:ℤ))) (.branch 161 (.leaf (3128179617196359:ℤ)) (.leaf (3745777056479213:ℤ)))), (.branch 149 (.branch 133 (.leaf (2023165386973498:ℤ)) (.leaf (2604844414836601:ℤ))) (.branch 161 (.leaf (3190647280887031:ℤ)) (.leaf (3843604282155793:ℤ)))), (.branch 149 (.branch 133 (.leaf (2020518490899671:ℤ)) (.leaf (2608369445855843:ℤ))) (.branch 161 (.leaf (3213792549558237:ℤ)) (.leaf (3910598649165379:ℤ)))), (.branch 149 (.branch 133 (.leaf (2037089075378983:ℤ)) (.leaf (2646959326801119:ℤ))) (.branch 161 (.leaf (3282398172292319:ℤ)) (.leaf (4021379459729006:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 35 20) 8000 (endpointMeanRuns 35 20) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 35 20, EndpointRunConditions (endpointMeanCutoff 35 20) (endpointMeanBox 35 20).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 20, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 35 20 h) (endpointMeanCornerA 35 20 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 20, endpointJoint24Q (endpointMeanCornerK 35 20 h) (endpointMeanCornerA 35 20 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 35 20, endpointRunWeightQ (endpointMeanCutoff 35 20) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 35 20) = (6170419/15625000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 35 20 h = (logRoundedQ ((endpointMeanCutoff 35 20:ℚ)/200)).2+(6170419/15625000000000:ℚ)+((endpointMeanRuns 35 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 35 20).map (fun r => endpointRunWeightQ (endpointMeanCutoff 35 20) r*endpointJoint24Q (endpointMeanCornerK 35 20 h) (endpointMeanCornerA 35 20 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 35 20).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 35 20 h≤endpointMeanCorner 35 20 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 35 20 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint35_20

namespace EndpointAnalyticJoint35_21
private noncomputable def weights : IntegerLookupTree := (.branch 1745 (.branch 1206 (.leaf (69511822700000:ℤ)) (.leaf (30941581200000:ℤ))) (.branch 2652 (.leaf (12803848100000:ℤ)) (.leaf (3442422900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 138 (.branch 125 (.leaf (2023165386973498:ℤ)) (.leaf (2385933105937302:ℤ))) (.branch 155 (.leaf (2763222926809541:ℤ)) (.leaf (3485974895894125:ℤ)))), (.branch 138 (.branch 125 (.leaf (2039091607166679:ℤ)) (.leaf (2413884905810278:ℤ))) (.branch 155 (.leaf (2806506508302274:ℤ)) (.leaf (3565510217449023:ℤ)))), (.branch 138 (.branch 125 (.leaf (2037089075378983:ℤ)) (.leaf (2415219999957960:ℤ))) (.branch 155 (.leaf (2816462203221370:ℤ)) (.leaf (3612276399464539:ℤ)))), (.branch 138 (.branch 125 (.leaf (2053795557783124:ℤ)) (.leaf (2444934892142196:ℤ))) (.branch 155 (.leaf (2863180478360135:ℤ)) (.leaf (3700960398189268:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 35 21) 8000 (endpointMeanRuns 35 21) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 35 21, EndpointRunConditions (endpointMeanCutoff 35 21) (endpointMeanBox 35 21).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 21, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 35 21 h) (endpointMeanCornerA 35 21 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 21, endpointJoint24Q (endpointMeanCornerK 35 21 h) (endpointMeanCornerA 35 21 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 35 21, endpointRunWeightQ (endpointMeanCutoff 35 21) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 35 21) = (393672309/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 35 21 h = (logRoundedQ ((endpointMeanCutoff 35 21:ℚ)/200)).2+(393672309/1000000000000000:ℚ)+((endpointMeanRuns 35 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 35 21).map (fun r => endpointRunWeightQ (endpointMeanCutoff 35 21) r*endpointJoint24Q (endpointMeanCornerK 35 21 h) (endpointMeanCornerA 35 21 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 35 21).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 35 21 h≤endpointMeanCorner 35 21 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 35 21 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint35_21

namespace EndpointAnalyticJoint35_22
private noncomputable def weights : IntegerLookupTree := (.branch 1579 (.leaf (112602896600000:ℤ)) (.branch 2652 (.leaf (21038975600000:ℤ)) (.leaf (3425218300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2039091607166679:ℤ)) (.branch 142 (.leaf (2413884905810278:ℤ)) (.leaf (2954267435313987:ℤ)))), (.branch 125 (.leaf (2055143197481000:ℤ)) (.branch 142 (.leaf (2442164167972196:ℤ)) (.leaf (3004816961466157:ℤ)))), (.branch 125 (.leaf (2053795557783124:ℤ)) (.branch 142 (.leaf (2444934892142196:ℤ)) (.leaf (3023093156984340:ℤ)))), (.branch 125 (.leaf (2070639052631978:ℤ)) (.branch 142 (.leaf (2475015372064837:ℤ)) (.leaf (3078040775780820:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 35 22) 8000 (endpointMeanRuns 35 22) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 35 22, EndpointRunConditions (endpointMeanCutoff 35 22) (endpointMeanBox 35 22).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 22, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 35 22 h) (endpointMeanCornerA 35 22 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 22, endpointJoint24Q (endpointMeanCornerK 35 22 h) (endpointMeanCornerA 35 22 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 35 22, endpointRunWeightQ (endpointMeanCutoff 35 22) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 35 22) = (392299133/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 35 22 h = (logRoundedQ ((endpointMeanCutoff 35 22:ℚ)/200)).2+(392299133/1000000000000000:ℚ)+((endpointMeanRuns 35 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 35 22).map (fun r => endpointRunWeightQ (endpointMeanCutoff 35 22) r*endpointJoint24Q (endpointMeanCornerK 35 22 h) (endpointMeanCornerA 35 22 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 35 22).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 35 22 h≤endpointMeanCorner 35 22 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 35 22 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint35_22

namespace EndpointAnalyticJoint35_23
private noncomputable def weights : IntegerLookupTree := (.branch 1053 (.leaf (42063254400000:ℤ)) (.branch 1745 (.leaf (52267663900000:ℤ)) (.leaf (33407113000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 138 (.leaf (2055143197481000:ℤ)) (.branch 163 (.leaf (2850468090982924:ℤ)) (.leaf (4200953002500134:ℤ)))), (.branch 138 (.leaf (2071321144821510:ℤ)) (.branch 163 (.leaf (2895118295174365:ℤ)) (.leaf (4315794643539089:ℤ)))), (.branch 138 (.leaf (2070639052631978:ℤ)) (.branch 163 (.leaf (2910673696343662:ℤ)) (.leaf (4433209227610516:ℤ)))), (.branch 138 (.leaf (2087620683585788:ℤ)) (.branch 163 (.leaf (2958954711593718:ℤ)) (.leaf (4565068323559783:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 35 23) 8000 (endpointMeanRuns 35 23) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 35 23, EndpointRunConditions (endpointMeanCutoff 35 23) (endpointMeanBox 35 23).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 23, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 35 23 h) (endpointMeanCornerA 35 23 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 23, endpointJoint24Q (endpointMeanCornerK 35 23 h) (endpointMeanCornerA 35 23 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 35 23, endpointRunWeightQ (endpointMeanCutoff 35 23) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 35 23) = (97773033/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 35 23 h = (logRoundedQ ((endpointMeanCutoff 35 23:ℚ)/200)).2+(97773033/250000000000000:ℚ)+((endpointMeanRuns 35 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 35 23).map (fun r => endpointRunWeightQ (endpointMeanCutoff 35 23) r*endpointJoint24Q (endpointMeanCornerK 35 23 h) (endpointMeanCornerA 35 23 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 35 23).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 35 23 h≤endpointMeanCorner 35 23 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 35 23 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint35_23

namespace EndpointAnalyticJoint35_24
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.leaf (94140710300000:ℤ)) (.branch 2652 (.leaf (28319230300000:ℤ)) (.leaf (3395130000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 125 (.leaf (2071321144821510:ℤ)) (.branch 145 (.leaf (2470774728725232:ℤ)) (.leaf (3189251797678758:ℤ)))), (.branch 125 (.leaf (2087626443862127:ℤ)) (.branch 145 (.leaf (2499720469314806:ℤ)) (.leaf (3247555114345552:ℤ)))), (.branch 125 (.leaf (2087620683585788:ℤ)) (.branch 145 (.leaf (2505465937618499:ℤ)) (.leaf (3279758079840817:ℤ)))), (.branch 125 (.leaf (2104741583520097:ℤ)) (.branch 145 (.leaf (2536291142034212:ℤ)) (.leaf (3343612244288027:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 35 24) 8000 (endpointMeanRuns 35 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 35 24, EndpointRunConditions (endpointMeanCutoff 35 24) (endpointMeanBox 35 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 35 24 h) (endpointMeanCornerA 35 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 24, endpointJoint24Q (endpointMeanCornerK 35 24 h) (endpointMeanCornerA 35 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 35 24, endpointRunWeightQ (endpointMeanCutoff 35 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 35 24) = (48737207/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 35 24 h = (logRoundedQ ((endpointMeanCutoff 35 24:ℚ)/200)).2+(48737207/125000000000000:ℚ)+((endpointMeanRuns 35 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 35 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 35 24) r*endpointJoint24Q (endpointMeanCornerK 35 24 h) (endpointMeanCornerA 35 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 35 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 35 24 h≤endpointMeanCorner 35 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 35 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint35_24

namespace EndpointAnalyticJoint35_25
private noncomputable def weights : IntegerLookupTree := (.branch 2009 (.leaf (140099766300000:ℤ)) (.leaf (17193902300000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 133 (.leaf (2087626443862127:ℤ)) (.leaf (2754023774904963:ℤ))), (.branch 133 (.leaf (2104060097106756:ℤ)) (.leaf (2792634887978791:ℤ))), (.branch 133 (.leaf (2104741583520097:ℤ)) (.leaf (2807113176363739:ℤ))), (.branch 133 (.leaf (2122002894601351:ℤ)) (.leaf (2848643398797490:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 35 25) 8000 (endpointMeanRuns 35 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 35 25, EndpointRunConditions (endpointMeanCutoff 35 25) (endpointMeanBox 35 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 35 25 h) (endpointMeanCornerA 35 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 25, endpointJoint24Q (endpointMeanCornerK 35 25 h) (endpointMeanCornerA 35 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 35 25, endpointRunWeightQ (endpointMeanCutoff 35 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 35 25) = (388715447/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 35 25 h = (logRoundedQ ((endpointMeanCutoff 35 25:ℚ)/200)).2+(388715447/1000000000000000:ℚ)+((endpointMeanRuns 35 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 35 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 35 25) r*endpointJoint24Q (endpointMeanCornerK 35 25 h) (endpointMeanCornerA 35 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 35 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 35 25 h≤endpointMeanCorner 35 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 35 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint35_25

namespace EndpointAnalyticJoint35_26
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.leaf (87942374300000:ℤ)) (.leaf (63477324000000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 145 (.leaf (2104060097106756:ℤ)) (.leaf (3306924284996283:ℤ))), (.branch 145 (.leaf (2120623114950957:ℤ)) (.leaf (3367378794709682:ℤ))), (.branch 145 (.leaf (2122002894601351:ℤ)) (.leaf (3408709596256388:ℤ))), (.branch 145 (.leaf (2139405768363065:ℤ)) (.leaf (3475074339573898:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 35 26) 8000 (endpointMeanRuns 35 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 35 26, EndpointRunConditions (endpointMeanCutoff 35 26) (endpointMeanBox 35 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 35 26 h) (endpointMeanCornerA 35 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 26, endpointJoint24Q (endpointMeanCornerK 35 26 h) (endpointMeanCornerA 35 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 35 26, endpointRunWeightQ (endpointMeanCutoff 35 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 35 26) = (77509051/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 35 26 h = (logRoundedQ ((endpointMeanCutoff 35 26:ℚ)/200)).2+(77509051/200000000000000:ℚ)+((endpointMeanRuns 35 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 35 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 35 26) r*endpointJoint24Q (endpointMeanCornerK 35 26 h) (endpointMeanCornerA 35 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 35 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 35 26 h≤endpointMeanCorner 35 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 35 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint35_26

namespace EndpointAnalyticJoint35_27
private noncomputable def weights : IntegerLookupTree := (.branch 2009 (.leaf (132176281800000:ℤ)) (.leaf (17028327800000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 133 (.leaf (2120623114950957:ℤ)) (.leaf (2831787324648439:ℤ))), (.branch 133 (.leaf (2137316515744048:ℤ)) (.leaf (2871488674211705:ℤ))), (.branch 133 (.leaf (2139405768363065:ℤ)) (.leaf (2890788045825847:ℤ))), (.branch 133 (.leaf (2156951365782668:ℤ)) (.leaf (2933556207638073:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 35 27) 8000 (endpointMeanRuns 35 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 35 27, EndpointRunConditions (endpointMeanCutoff 35 27) (endpointMeanBox 35 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 35 27 h) (endpointMeanCornerA 35 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 27, endpointJoint24Q (endpointMeanCornerK 35 27 h) (endpointMeanCornerA 35 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 35 27, endpointRunWeightQ (endpointMeanCutoff 35 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 35 27) = (386386839/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 35 27 h = (logRoundedQ ((endpointMeanCutoff 35 27:ℚ)/200)).2+(386386839/1000000000000000:ℚ)+((endpointMeanRuns 35 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 35 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 35 27) r*endpointJoint24Q (endpointMeanCornerK 35 27 h) (endpointMeanCornerA 35 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 35 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 35 27 h≤endpointMeanCorner 35 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 35 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint35_27

namespace EndpointAnalyticJoint35_28
private noncomputable def weights : IntegerLookupTree := (.branch 1579 (.leaf (92255696500000:ℤ)) (.leaf (48743482600000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 142 (.leaf (2137316515744048:ℤ)) (.leaf (3270838461782982:ℤ))), (.branch 142 (.leaf (2154141325851730:ℤ)) (.leaf (3326804733619785:ℤ))), (.branch 142 (.leaf (2156951365782668:ℤ)) (.leaf (3368127796388545:ℤ))), (.branch 142 (.leaf (2174640857358941:ℤ)) (.leaf (3429346750818118:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 35 28) 8000 (endpointMeanRuns 35 28) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 35 28, EndpointRunConditions (endpointMeanCutoff 35 28) (endpointMeanBox 35 28).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 28, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 35 28 h) (endpointMeanCornerA 35 28 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 35 28, endpointJoint24Q (endpointMeanCornerK 35 28 h) (endpointMeanCornerA 35 28 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 35 28, endpointRunWeightQ (endpointMeanCutoff 35 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 35 28) = (77019481/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 35 28 h = (logRoundedQ ((endpointMeanCutoff 35 28:ℚ)/200)).2+(77019481/200000000000000:ℚ)+((endpointMeanRuns 35 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 35 28).map (fun r => endpointRunWeightQ (endpointMeanCutoff 35 28) r*endpointJoint24Q (endpointMeanCornerK 35 28 h) (endpointMeanCornerA 35 28 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 35 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 35 28 h≤endpointMeanCorner 35 28 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 35 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint35_28

private theorem activeIndices30 : ∀ai : Fin 42, endpointMeanActive 30 ai → ai∈
    ([9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow30 (ai : Fin 42) : endpointMeanActive 30 ai →
    EndpointJointNumericalConditions 30 ai := by
  intro hact
  have hi := activeIndices30 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint30_09.conditions
  · exact EndpointAnalyticJoint30_10.conditions
  · exact EndpointAnalyticJoint30_11.conditions
  · exact EndpointAnalyticJoint30_12.conditions
  · exact EndpointAnalyticJoint30_13.conditions
  · exact EndpointAnalyticJoint30_14.conditions
  · exact EndpointAnalyticJoint30_15.conditions
  · exact EndpointAnalyticJoint30_16.conditions
  · exact EndpointAnalyticJoint30_17.conditions
  · exact EndpointAnalyticJoint30_18.conditions
  · exact EndpointAnalyticJoint30_19.conditions
  · exact EndpointAnalyticJoint30_20.conditions
  · exact EndpointAnalyticJoint30_21.conditions
  · exact EndpointAnalyticJoint30_22.conditions
  · exact EndpointAnalyticJoint30_23.conditions
  · exact EndpointAnalyticJoint30_24.conditions
  · exact EndpointAnalyticJoint30_25.conditions

private theorem activeIndices31 : ∀ai : Fin 42, endpointMeanActive 31 ai → ai∈
    ([10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow31 (ai : Fin 42) : endpointMeanActive 31 ai →
    EndpointJointNumericalConditions 31 ai := by
  intro hact
  have hi := activeIndices31 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint31_10.conditions
  · exact EndpointAnalyticJoint31_11.conditions
  · exact EndpointAnalyticJoint31_12.conditions
  · exact EndpointAnalyticJoint31_13.conditions
  · exact EndpointAnalyticJoint31_14.conditions
  · exact EndpointAnalyticJoint31_15.conditions
  · exact EndpointAnalyticJoint31_16.conditions
  · exact EndpointAnalyticJoint31_17.conditions
  · exact EndpointAnalyticJoint31_18.conditions
  · exact EndpointAnalyticJoint31_19.conditions
  · exact EndpointAnalyticJoint31_20.conditions
  · exact EndpointAnalyticJoint31_21.conditions
  · exact EndpointAnalyticJoint31_22.conditions
  · exact EndpointAnalyticJoint31_23.conditions
  · exact EndpointAnalyticJoint31_24.conditions
  · exact EndpointAnalyticJoint31_25.conditions
  · exact EndpointAnalyticJoint31_26.conditions

private theorem activeIndices32 : ∀ai : Fin 42, endpointMeanActive 32 ai → ai∈
    ([10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow32 (ai : Fin 42) : endpointMeanActive 32 ai →
    EndpointJointNumericalConditions 32 ai := by
  intro hact
  have hi := activeIndices32 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint32_10.conditions
  · exact EndpointAnalyticJoint32_11.conditions
  · exact EndpointAnalyticJoint32_12.conditions
  · exact EndpointAnalyticJoint32_13.conditions
  · exact EndpointAnalyticJoint32_14.conditions
  · exact EndpointAnalyticJoint32_15.conditions
  · exact EndpointAnalyticJoint32_16.conditions
  · exact EndpointAnalyticJoint32_17.conditions
  · exact EndpointAnalyticJoint32_18.conditions
  · exact EndpointAnalyticJoint32_19.conditions
  · exact EndpointAnalyticJoint32_20.conditions
  · exact EndpointAnalyticJoint32_21.conditions
  · exact EndpointAnalyticJoint32_22.conditions
  · exact EndpointAnalyticJoint32_23.conditions
  · exact EndpointAnalyticJoint32_24.conditions
  · exact EndpointAnalyticJoint32_25.conditions
  · exact EndpointAnalyticJoint32_26.conditions

private theorem activeIndices33 : ∀ai : Fin 42, endpointMeanActive 33 ai → ai∈
    ([11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow33 (ai : Fin 42) : endpointMeanActive 33 ai →
    EndpointJointNumericalConditions 33 ai := by
  intro hact
  have hi := activeIndices33 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint33_11.conditions
  · exact EndpointAnalyticJoint33_12.conditions
  · exact EndpointAnalyticJoint33_13.conditions
  · exact EndpointAnalyticJoint33_14.conditions
  · exact EndpointAnalyticJoint33_15.conditions
  · exact EndpointAnalyticJoint33_16.conditions
  · exact EndpointAnalyticJoint33_17.conditions
  · exact EndpointAnalyticJoint33_18.conditions
  · exact EndpointAnalyticJoint33_19.conditions
  · exact EndpointAnalyticJoint33_20.conditions
  · exact EndpointAnalyticJoint33_21.conditions
  · exact EndpointAnalyticJoint33_22.conditions
  · exact EndpointAnalyticJoint33_23.conditions
  · exact EndpointAnalyticJoint33_24.conditions
  · exact EndpointAnalyticJoint33_25.conditions
  · exact EndpointAnalyticJoint33_26.conditions
  · exact EndpointAnalyticJoint33_27.conditions

private theorem activeIndices34 : ∀ai : Fin 42, endpointMeanActive 34 ai → ai∈
    ([12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow34 (ai : Fin 42) : endpointMeanActive 34 ai →
    EndpointJointNumericalConditions 34 ai := by
  intro hact
  have hi := activeIndices34 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint34_12.conditions
  · exact EndpointAnalyticJoint34_13.conditions
  · exact EndpointAnalyticJoint34_14.conditions
  · exact EndpointAnalyticJoint34_15.conditions
  · exact EndpointAnalyticJoint34_16.conditions
  · exact EndpointAnalyticJoint34_17.conditions
  · exact EndpointAnalyticJoint34_18.conditions
  · exact EndpointAnalyticJoint34_19.conditions
  · exact EndpointAnalyticJoint34_20.conditions
  · exact EndpointAnalyticJoint34_21.conditions
  · exact EndpointAnalyticJoint34_22.conditions
  · exact EndpointAnalyticJoint34_23.conditions
  · exact EndpointAnalyticJoint34_24.conditions
  · exact EndpointAnalyticJoint34_25.conditions
  · exact EndpointAnalyticJoint34_26.conditions
  · exact EndpointAnalyticJoint34_27.conditions

private theorem activeIndices35 : ∀ai : Fin 42, endpointMeanActive 35 ai → ai∈
    ([12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow35 (ai : Fin 42) : endpointMeanActive 35 ai →
    EndpointJointNumericalConditions 35 ai := by
  intro hact
  have hi := activeIndices35 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint35_12.conditions
  · exact EndpointAnalyticJoint35_13.conditions
  · exact EndpointAnalyticJoint35_14.conditions
  · exact EndpointAnalyticJoint35_15.conditions
  · exact EndpointAnalyticJoint35_16.conditions
  · exact EndpointAnalyticJoint35_17.conditions
  · exact EndpointAnalyticJoint35_18.conditions
  · exact EndpointAnalyticJoint35_19.conditions
  · exact EndpointAnalyticJoint35_20.conditions
  · exact EndpointAnalyticJoint35_21.conditions
  · exact EndpointAnalyticJoint35_22.conditions
  · exact EndpointAnalyticJoint35_23.conditions
  · exact EndpointAnalyticJoint35_24.conditions
  · exact EndpointAnalyticJoint35_25.conditions
  · exact EndpointAnalyticJoint35_26.conditions
  · exact EndpointAnalyticJoint35_27.conditions
  · exact EndpointAnalyticJoint35_28.conditions

end SingularValueBounds.KL.Certificates
