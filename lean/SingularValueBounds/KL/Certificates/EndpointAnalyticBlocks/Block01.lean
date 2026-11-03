import SingularValueBounds.KL.Certificates.EndpointAnalyticLogs
import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SingularValueBounds.KL.Certificates

namespace EndpointAnalyticJoint06_01
private noncomputable def weights : IntegerLookupTree := (.branch 1375 (.leaf (167295826200000:ℤ)) (.branch 2750 (.leaf (18095748300000:ℤ)) (.leaf (1652868900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 150 (.leaf (1802482738256921:ℤ)) (.branch 200 (.leaf (2131932292346563:ℤ)) (.leaf (2753927108800162:ℤ)))), (.branch 150 (.leaf (1805913348452187:ℤ)) (.branch 200 (.leaf (2138784322011830:ℤ)) (.leaf (2770355346494974:ℤ)))), (.branch 150 (.leaf (1802828170512209:ℤ)) (.branch 200 (.leaf (2132659094351735:ℤ)) (.leaf (2755816313808364:ℤ)))), (.branch 150 (.leaf (1806417461107969:ℤ)) (.branch 200 (.leaf (2139846417135852:ℤ)) (.leaf (2773123881633043:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 6 1) 8000 (endpointMeanRuns 6 1) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 6 1, EndpointRunConditions (endpointMeanCutoff 6 1) (endpointMeanBox 6 1).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 1, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 6 1 h) (endpointMeanCornerA 6 1 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 1, endpointJoint24Q (endpointMeanCornerK 6 1 h) (endpointMeanCornerA 6 1 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 6 1, endpointRunWeightQ (endpointMeanCutoff 6 1) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 6 1) = (461797707/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 6 1 h = (logRoundedQ ((endpointMeanCutoff 6 1:ℚ)/200)).2+(461797707/1000000000000000:ℚ)+((endpointMeanRuns 6 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 6 1).map (fun r => endpointRunWeightQ (endpointMeanCutoff 6 1) r*endpointJoint24Q (endpointMeanCornerK 6 1 h) (endpointMeanCornerA 6 1 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 6 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 6 1 h≤endpointMeanCorner 6 1 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 6 1 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint06_01

namespace EndpointAnalyticJoint06_02
private noncomputable def weights : IntegerLookupTree := (.branch 1375 (.leaf (163623955500000:ℤ)) (.branch 2750 (.leaf (18022186300000:ℤ)) (.leaf (1647588200000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 150 (.leaf (1805913348452187:ℤ)) (.branch 200 (.leaf (2138784322011830:ℤ)) (.leaf (2770355346494974:ℤ)))), (.branch 150 (.leaf (1811399427747628:ℤ)) (.branch 200 (.leaf (2149760392733081:ℤ)) (.leaf (2796765004917941:ℤ)))), (.branch 150 (.leaf (1806417461107969:ℤ)) (.branch 200 (.leaf (2139846417135852:ℤ)) (.leaf (2773123881633043:ℤ)))), (.branch 150 (.leaf (1812157946781294:ℤ)) (.branch 200 (.leaf (2151361910082970:ℤ)) (.leaf (2800958443319509:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 6 2) 8000 (endpointMeanRuns 6 2) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 6 2, EndpointRunConditions (endpointMeanCutoff 6 2) (endpointMeanBox 6 2).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 2, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 6 2 h) (endpointMeanCornerA 6 2 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 2, endpointJoint24Q (endpointMeanCornerK 6 2 h) (endpointMeanCornerA 6 2 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 6 2, endpointRunWeightQ (endpointMeanCutoff 6 2) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 6 2) = (460693463/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 6 2 h = (logRoundedQ ((endpointMeanCutoff 6 2:ℚ)/200)).2+(460693463/1000000000000000:ℚ)+((endpointMeanRuns 6 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 6 2).map (fun r => endpointRunWeightQ (endpointMeanCutoff 6 2) r*endpointJoint24Q (endpointMeanCornerK 6 2 h) (endpointMeanCornerA 6 2 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 6 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 6 2 h≤endpointMeanCorner 6 2 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 6 2 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint06_02

namespace EndpointAnalyticJoint06_03
private noncomputable def weights : IntegerLookupTree := (.branch 1375 (.leaf (160036135500000:ℤ)) (.branch 2750 (.leaf (17949323300000:ℤ)) (.leaf (1642357800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 150 (.leaf (1811399427747628:ℤ)) (.branch 200 (.leaf (2149760392733081:ℤ)) (.leaf (2796765004917941:ℤ)))), (.branch 150 (.leaf (1816902172884795:ℤ)) (.branch 200 (.leaf (2160792791774692:ℤ)) (.leaf (2823426425288662:ℤ)))), (.branch 150 (.leaf (1812157946781294:ℤ)) (.branch 200 (.leaf (2151361910082970:ℤ)) (.leaf (2800958443319509:ℤ)))), (.branch 150 (.leaf (1817916674736080:ℤ)) (.branch 200 (.leaf (2162939373168110:ℤ)) (.leaf (2829072387701219:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 6 3) 8000 (endpointMeanRuns 6 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 6 3, EndpointRunConditions (endpointMeanCutoff 6 3) (endpointMeanBox 6 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 6 3 h) (endpointMeanCornerA 6 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 3, endpointJoint24Q (endpointMeanCornerK 6 3 h) (endpointMeanCornerA 6 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 6 3, endpointRunWeightQ (endpointMeanCutoff 6 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 6 3) = (45959971/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 6 3 h = (logRoundedQ ((endpointMeanCutoff 6 3:ℚ)/200)).2+(45959971/100000000000000:ℚ)+((endpointMeanRuns 6 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 6 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 6 3) r*endpointJoint24Q (endpointMeanCornerK 6 3 h) (endpointMeanCornerA 6 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 6 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 6 3 h≤endpointMeanCorner 6 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 6 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint06_03

namespace EndpointAnalyticJoint06_04
private noncomputable def weights : IntegerLookupTree := (.branch 1698 (.branch 1375 (.leaf (155666365700000:ℤ)) (.leaf (3810167500000:ℤ))) (.branch 2696 (.leaf (5351725300000:ℤ)) (.leaf (1904317900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 181 (.branch 151 (.leaf (1816902172884795:ℤ)) (.leaf (2172255384679391:ℤ))) (.branch 200 (.leaf (2548706482177401:ℤ)) (.leaf (2823426425288662:ℤ)))), (.branch 181 (.branch 151 (.leaf (1822421634491879:ℤ)) (.leaf (2183561958860165:ℤ))) (.branch 200 (.leaf (2568269846507507:ℤ)) (.leaf (2850342007641147:ℤ)))), (.branch 181 (.branch 151 (.leaf (1817916674736080:ℤ)) (.leaf (2174447549274820:ℤ))) (.branch 200 (.leaf (2552685723754059:ℤ)) (.leaf (2829072387701219:ℤ)))), (.branch 181 (.branch 151 (.leaf (1823693702943180:ℤ)) (.leaf (2186316774732912:ℤ))) (.branch 200 (.leaf (2573283056117434:ℤ)) (.leaf (2857468519014538:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 6 4) 8000 (endpointMeanRuns 6 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 6 4, EndpointRunConditions (endpointMeanCutoff 6 4) (endpointMeanBox 6 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 6 4 h) (endpointMeanCornerA 6 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 4, endpointJoint24Q (endpointMeanCornerK 6 4 h) (endpointMeanCornerA 6 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 6 4, endpointRunWeightQ (endpointMeanCutoff 6 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 6 4) = (458246973/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 6 4 h = (logRoundedQ ((endpointMeanCutoff 6 4:ℚ)/200)).2+(458246973/1000000000000000:ℚ)+((endpointMeanRuns 6 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 6 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 6 4) r*endpointJoint24Q (endpointMeanCornerK 6 4 h) (endpointMeanCornerA 6 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 6 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 6 4 h≤endpointMeanCorner 6 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 6 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint06_04

namespace EndpointAnalyticJoint06_05
private noncomputable def weights : IntegerLookupTree := (.branch 1698 (.branch 1375 (.leaf (152260079100000:ℤ)) (.leaf (3794419700000:ℤ))) (.branch 2750 (.leaf (5626265100000:ℤ)) (.leaf (1630767900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 181 (.branch 150 (.leaf (1822421634491879:ℤ)) (.leaf (2171881808209113:ℤ))) (.branch 200 (.leaf (2568269846507507:ℤ)) (.leaf (2850342007641147:ℤ)))), (.branch 181 (.branch 150 (.leaf (1827957863350873:ℤ)) (.leaf (2183027732592306:ℤ))) (.branch 200 (.leaf (2587983375333439:ℤ)) (.leaf (2877514174888818:ℤ)))), (.branch 181 (.branch 150 (.leaf (1823693702943180:ℤ)) (.leaf (2174579139880947:ℤ))) (.branch 200 (.leaf (2573283056117434:ℤ)) (.leaf (2857468519014538:ℤ)))), (.branch 181 (.branch 150 (.leaf (1829489089557665:ℤ)) (.leaf (2186281545505821:ℤ))) (.branch 200 (.leaf (2594046586025818:ℤ)) (.leaf (2886149669642689:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 6 5) 8000 (endpointMeanRuns 6 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 6 5, EndpointRunConditions (endpointMeanCutoff 6 5) (endpointMeanBox 6 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 6 5 h) (endpointMeanCornerA 6 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 5, endpointJoint24Q (endpointMeanCornerK 6 5 h) (endpointMeanCornerA 6 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 6 5, endpointRunWeightQ (endpointMeanCutoff 6 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 6 5) = (457176113/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 6 5 h = (logRoundedQ ((endpointMeanCutoff 6 5:ℚ)/200)).2+(457176113/1000000000000000:ℚ)+((endpointMeanRuns 6 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 6 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 6 5) r*endpointJoint24Q (endpointMeanCornerK 6 5 h) (endpointMeanCornerA 6 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 6 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 6 5 h≤endpointMeanCorner 6 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 6 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint06_05

namespace EndpointAnalyticJoint06_06
private noncomputable def weights : IntegerLookupTree := (.branch 1698 (.branch 1375 (.leaf (148110907300000:ℤ)) (.leaf (3774938800000:ℤ))) (.branch 2750 (.leaf (5600341500000:ℤ)) (.leaf (1624432900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 181 (.branch 150 (.leaf (1827957863350873:ℤ)) (.leaf (2183027732592306:ℤ))) (.branch 200 (.leaf (2587983375333439:ℤ)) (.leaf (2877514174888818:ℤ)))), (.branch 181 (.branch 150 (.leaf (1833510910398045:ℤ)) (.leaf (2194230856971319:ℤ))) (.branch 200 (.leaf (2607848221288020:ℤ)) (.leaf (2904945373042581:ℤ)))), (.branch 181 (.branch 150 (.leaf (1829489089557665:ℤ)) (.leaf (2186281545505821:ℤ))) (.branch 200 (.leaf (2594046586025818:ℤ)) (.leaf (2886149669642689:ℤ)))), (.branch 181 (.branch 150 (.leaf (1835302892919412:ℤ)) (.leaf (2198046927131378:ℤ))) (.branch 200 (.leaf (2614977654508409:ℤ)) (.leaf (2915118700398267:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 6 6) 8000 (endpointMeanRuns 6 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 6 6, EndpointRunConditions (endpointMeanCutoff 6 6) (endpointMeanBox 6 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 6 6 h) (endpointMeanCornerA 6 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 6, endpointJoint24Q (endpointMeanCornerK 6 6 h) (endpointMeanCornerA 6 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 6 6, endpointRunWeightQ (endpointMeanCutoff 6 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 6 6) = (113962849/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 6 6 h = (logRoundedQ ((endpointMeanCutoff 6 6:ℚ)/200)).2+(113962849/250000000000000:ℚ)+((endpointMeanRuns 6 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 6 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 6 6) r*endpointJoint24Q (endpointMeanCornerK 6 6 h) (endpointMeanCornerA 6 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 6 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 6 6 h≤endpointMeanCorner 6 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 6 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint06_06

namespace EndpointAnalyticJoint06_07
private noncomputable def weights : IntegerLookupTree := (.branch 1698 (.branch 1375 (.leaf (144876199400000:ℤ)) (.leaf (3759513900000:ℤ))) (.branch 2750 (.leaf (5579815300000:ℤ)) (.leaf (1619416900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 181 (.branch 150 (.leaf (1833510910398045:ℤ)) (.leaf (2194230856971319:ℤ))) (.branch 200 (.leaf (2607848221288020:ℤ)) (.leaf (2904945373042581:ℤ)))), (.branch 181 (.branch 150 (.leaf (1839080826724384:ℤ)) (.leaf (2205491474891975:ℤ))) (.branch 200 (.leaf (2627865545851454:ℤ)) (.leaf (2932638071431067:ℤ)))), (.branch 181 (.branch 150 (.leaf (1835302892919412:ℤ)) (.leaf (2198046927131378:ℤ))) (.branch 200 (.leaf (2614977654508409:ℤ)) (.leaf (2915118700398267:ℤ)))), (.branch 181 (.branch 150 (.leaf (1841135171553694:ℤ)) (.leaf (2209875623660306:ℤ))) (.branch 200 (.leaf (2636077613415022:ℤ)) (.leaf (2944378500808566:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 6 7) 8000 (endpointMeanRuns 6 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 6 7, EndpointRunConditions (endpointMeanCutoff 6 7) (endpointMeanBox 6 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 6 7 h) (endpointMeanCornerA 6 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 7, endpointJoint24Q (endpointMeanCornerK 6 7 h) (endpointMeanCornerA 6 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 6 7, endpointRunWeightQ (endpointMeanCutoff 6 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 6 7) = (45480249/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 6 7 h = (logRoundedQ ((endpointMeanCutoff 6 7:ℚ)/200)).2+(45480249/100000000000000:ℚ)+((endpointMeanRuns 6 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 6 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 6 7) r*endpointJoint24Q (endpointMeanCornerK 6 7 h) (endpointMeanCornerA 6 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 6 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 6 7 h≤endpointMeanCorner 6 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 6 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint06_07

namespace EndpointAnalyticJoint06_08
private noncomputable def weights : IntegerLookupTree := (.branch 1698 (.branch 1375 (.leaf (140935577500000:ℤ)) (.leaf (3740428200000:ℤ))) (.branch 2084 (.leaf (2031093800000:ℤ)) (.branch 2750 (.leaf (1305508600000:ℤ)) (.leaf (1613210500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 150 (.leaf (1839080826724384:ℤ)) (.leaf (2205491474891975:ℤ))) (.branch 181 (.leaf (2412863496586037:ℤ)) (.branch 200 (.leaf (2627865545851454:ℤ)) (.leaf (2932638071431067:ℤ))))), (.branch 166 (.branch 150 (.leaf (1844667663576099:ℤ)) (.leaf (2216809881406544:ℤ))) (.branch 181 (.leaf (2428238243949765:ℤ)) (.branch 200 (.leaf (2648036519419226:ℤ)) (.leaf (2960594762922886:ℤ))))), (.branch 166 (.branch 150 (.leaf (1841135171553694:ℤ)) (.leaf (2209875623660306:ℤ))) (.branch 181 (.leaf (2418973160008358:ℤ)) (.branch 200 (.leaf (2636077613415022:ℤ)) (.leaf (2944378500808566:ℤ))))), (.branch 166 (.branch 150 (.leaf (1846985984171767:ℤ)) (.leaf (2221767975819080:ℤ))) (.branch 181 (.leaf (2435156506255357:ℤ)) (.branch 200 (.leaf (2657347825503370:ℤ)) (.leaf (2973931989403816:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 6 8) 8000 (endpointMeanRuns 6 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 6 8, EndpointRunConditions (endpointMeanCutoff 6 8) (endpointMeanBox 6 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 6 8 h) (endpointMeanCornerA 6 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 8, endpointJoint24Q (endpointMeanCornerK 6 8 h) (endpointMeanCornerA 6 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 6 8, endpointRunWeightQ (endpointMeanCutoff 6 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 6 8) = (453504657/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 6 8 h = (logRoundedQ ((endpointMeanCutoff 6 8:ℚ)/200)).2+(453504657/1000000000000000:ℚ)+((endpointMeanRuns 6 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 6 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 6 8) r*endpointJoint24Q (endpointMeanCornerK 6 8 h) (endpointMeanCornerA 6 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 6 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 6 8 h≤endpointMeanCorner 6 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 6 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint06_08

namespace EndpointAnalyticJoint06_09
private noncomputable def weights : IntegerLookupTree := (.branch 2084 (.branch 1375 (.leaf (137105887800000:ℤ)) (.branch 1698 (.leaf (3721555400000:ℤ)) (.leaf (2021721200000:ℤ)))) (.branch 2750 (.leaf (1299981800000:ℤ)) (.branch 4044 (.leaf (427909700000:ℤ)) (.leaf (40924500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 134 (.leaf (1844667663576099:ℤ)) (.branch 150 (.leaf (2026467699913909:ℤ)) (.leaf (2216809881406544:ℤ)))) (.branch 181 (.leaf (2428238243949765:ℤ)) (.branch 200 (.leaf (2648036519419226:ℤ)) (.leaf (2960594762922886:ℤ))))), (.branch 166 (.branch 134 (.leaf (1850271472355070:ℤ)) (.branch 150 (.leaf (2034656320013544:ℤ)) (.leaf (2228186373081494:ℤ)))) (.branch 181 (.leaf (2443710959083667:ℤ)) (.branch 200 (.leaf (2668362321370563:ℤ)) (.leaf (2988817964151035:ℤ))))), (.branch 166 (.branch 134 (.leaf (1846985984171767:ℤ)) (.branch 150 (.leaf (2029947059706314:ℤ)) (.leaf (2221767975819080:ℤ)))) (.branch 181 (.leaf (2435156506255357:ℤ)) (.branch 200 (.leaf (2657347825503370:ℤ)) (.leaf (2973931989403816:ℤ))))), (.branch 166 (.branch 134 (.leaf (1852855389671460:ℤ)) (.branch 150 (.leaf (2038538267085190:ℤ)) (.leaf (2233724326167775:ℤ)))) (.branch 181 (.leaf (2451448121870568:ℤ)) (.branch 200 (.leaf (2678789664527124:ℤ)) (.leaf (3003782114008306:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 6 9) 8000 (endpointMeanRuns 6 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 6 9, EndpointRunConditions (endpointMeanCutoff 6 9) (endpointMeanBox 6 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 6 9 h) (endpointMeanCornerA 6 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 9, endpointJoint24Q (endpointMeanCornerK 6 9 h) (endpointMeanCornerA 6 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 6 9, endpointRunWeightQ (endpointMeanCutoff 6 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 6 9) = (113055323/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 6 9 h = (logRoundedQ ((endpointMeanCutoff 6 9:ℚ)/200)).2+(113055323/250000000000000:ℚ)+((endpointMeanRuns 6 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 6 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 6 9) r*endpointJoint24Q (endpointMeanCornerK 6 9 h) (endpointMeanCornerA 6 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 6 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 6 9 h≤endpointMeanCorner 6 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 6 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint06_09

namespace EndpointAnalyticJoint06_10
private noncomputable def weights : IntegerLookupTree := (.branch 1698 (.branch 1375 (.leaf (134119741000000:ℤ)) (.leaf (3706607200000:ℤ))) (.branch 2084 (.leaf (2014297600000:ℤ)) (.branch 2750 (.leaf (1295604300000:ℤ)) (.leaf (1602212300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 150 (.leaf (1850271472355070:ℤ)) (.leaf (2228186373081494:ℤ))) (.branch 181 (.leaf (2443710959083667:ℤ)) (.branch 200 (.leaf (2668362321370563:ℤ)) (.leaf (2988817964151035:ℤ))))), (.branch 166 (.branch 150 (.leaf (1855892304619325:ℤ)) (.leaf (2239621248005238:ℤ))) (.branch 181 (.leaf (2459282266237616:ℤ)) (.branch 200 (.leaf (2688844140137349:ℤ)) (.leaf (3017310215739451:ℤ))))), (.branch 166 (.branch 150 (.leaf (1852855389671460:ℤ)) (.leaf (2233724326167775:ℤ))) (.branch 181 (.leaf (2451448121870568:ℤ)) (.branch 200 (.leaf (2678789664527124:ℤ)) (.leaf (3003782114008306:ℤ))))), (.branch 166 (.branch 150 (.leaf (1858743447137769:ℤ)) (.leaf (2245745019109944:ℤ))) (.branch 181 (.leaf (2467848731194671:ℤ)) (.branch 200 (.leaf (2700404515324614:ℤ)) (.leaf (3033931852034371:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 6 10) 8000 (endpointMeanRuns 6 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 6 10, EndpointRunConditions (endpointMeanCutoff 6 10) (endpointMeanBox 6 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 6 10 h) (endpointMeanCornerA 6 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 10, endpointJoint24Q (endpointMeanCornerK 6 10 h) (endpointMeanCornerA 6 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 6 10, endpointRunWeightQ (endpointMeanCutoff 6 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 6 10) = (451204803/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 6 10 h = (logRoundedQ ((endpointMeanCutoff 6 10:ℚ)/200)).2+(451204803/1000000000000000:ℚ)+((endpointMeanRuns 6 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 6 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 6 10) r*endpointJoint24Q (endpointMeanCornerK 6 10 h) (endpointMeanCornerA 6 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 6 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 6 10 h≤endpointMeanCorner 6 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 6 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint06_10

namespace EndpointAnalyticJoint06_11
private noncomputable def weights : IntegerLookupTree := (.branch 1698 (.branch 1375 (.leaf (130481323200000:ℤ)) (.leaf (3688105600000:ℤ))) (.branch 2084 (.leaf (2005109400000:ℤ)) (.branch 2750 (.leaf (1290186200000:ℤ)) (.leaf (1596195800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 150 (.leaf (1855892304619325:ℤ)) (.leaf (2239621248005238:ℤ))) (.branch 181 (.leaf (2459282266237616:ℤ)) (.branch 200 (.leaf (2688844140137349:ℤ)) (.leaf (3017310215739451:ℤ))))), (.branch 166 (.branch 150 (.leaf (1861530212083527:ℤ)) (.leaf (2251114805795950:ℤ))) (.branch 181 (.leaf (2474952793639185:ℤ)) (.branch 200 (.leaf (2709483173273650:ℤ)) (.leaf (3046074082531708:ℤ))))), (.branch 166 (.branch 150 (.leaf (1858743447137769:ℤ)) (.leaf (2245745019109944:ℤ))) (.branch 181 (.leaf (2467848731194671:ℤ)) (.branch 200 (.leaf (2700404515324614:ℤ)) (.leaf (3033931852034371:ℤ))))), (.branch 166 (.branch 150 (.leaf (1864650215843457:ℤ)) (.leaf (2257830400902533:ℤ))) (.branch 181 (.leaf (2484359063414316:ℤ)) (.branch 200 (.leaf (2722193773908269:ℤ)) (.leaf (3064384210779436:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 6 11) 8000 (endpointMeanRuns 6 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 6 11, EndpointRunConditions (endpointMeanCutoff 6 11) (endpointMeanBox 6 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 6 11 h) (endpointMeanCornerA 6 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 11, endpointJoint24Q (endpointMeanCornerK 6 11 h) (endpointMeanCornerA 6 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 6 11, endpointRunWeightQ (endpointMeanCutoff 6 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 6 11) = (224973343/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 6 11 h = (logRoundedQ ((endpointMeanCutoff 6 11:ℚ)/200)).2+(224973343/500000000000000:ℚ)+((endpointMeanRuns 6 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 6 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 6 11) r*endpointJoint24Q (endpointMeanCornerK 6 11 h) (endpointMeanCornerA 6 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 6 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 6 11 h≤endpointMeanCorner 6 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 6 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint06_11

namespace EndpointAnalyticJoint06_12
private noncomputable def weights : IntegerLookupTree := (.branch 1698 (.branch 1375 (.leaf (127644028500000:ℤ)) (.leaf (3673448600000:ℤ))) (.branch 2084 (.leaf (1997830400000:ℤ)) (.branch 2750 (.leaf (1285894000000:ℤ)) (.leaf (1591429600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 150 (.leaf (1861530212083527:ℤ)) (.leaf (2251114805795950:ℤ))) (.branch 181 (.leaf (2474952793639185:ℤ)) (.branch 200 (.leaf (2709483173273650:ℤ)) (.leaf (3046074082531708:ℤ))))), (.branch 166 (.branch 150 (.leaf (1867185246619432:ℤ)) (.leaf (2262667347609433:ℤ))) (.branch 181 (.leaf (2490723173519023:ℤ)) (.branch 200 (.leaf (2730280627525721:ℤ)) (.leaf (3075112153821908:ℤ))))), (.branch 166 (.branch 150 (.leaf (1864650215843457:ℤ)) (.leaf (2257830400902533:ℤ))) (.branch 181 (.leaf (2484359063414316:ℤ)) (.branch 200 (.leaf (2722193773908269:ℤ)) (.leaf (3064384210779436:ℤ))))), (.branch 166 (.branch 150 (.leaf (1870575755249636:ℤ)) (.leaf (2269980819665848:ℤ))) (.branch 181 (.leaf (2500979852594537:ℤ)) (.branch 200 (.leaf (2744158847554790:ℤ)) (.leaf (3095142227725925:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 6 12) 8000 (endpointMeanRuns 6 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 6 12, EndpointRunConditions (endpointMeanCutoff 6 12) (endpointMeanBox 6 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 6 12 h) (endpointMeanCornerA 6 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 12, endpointJoint24Q (endpointMeanCornerK 6 12 h) (endpointMeanCornerA 6 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 6 12, endpointRunWeightQ (endpointMeanCutoff 6 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 6 12) = (448949999/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 6 12 h = (logRoundedQ ((endpointMeanCutoff 6 12:ℚ)/200)).2+(448949999/1000000000000000:ℚ)+((endpointMeanRuns 6 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 6 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 6 12) r*endpointJoint24Q (endpointMeanCornerK 6 12 h) (endpointMeanCornerA 6 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 6 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 6 12 h≤endpointMeanCorner 6 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 6 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint06_12

namespace EndpointAnalyticJoint06_13
private noncomputable def weights : IntegerLookupTree := (.branch 1698 (.branch 1375 (.leaf (124186634500000:ℤ)) (.leaf (3655304000000:ℤ))) (.branch 2084 (.leaf (1988819400000:ℤ)) (.branch 2696 (.leaf (1183489300000:ℤ)) (.leaf (1845341400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 151 (.leaf (1867185246619432:ℤ)) (.leaf (2276159107931052:ℤ))) (.branch 181 (.leaf (2490723173519023:ℤ)) (.branch 200 (.leaf (2730280627525721:ℤ)) (.leaf (3075112153821908:ℤ))))), (.branch 166 (.branch 151 (.leaf (1872857460256375:ℤ)) (.leaf (2288006500269254:ℤ))) (.branch 181 (.leaf (2506594042136340:ℤ)) (.branch 200 (.leaf (2751237718902549:ℤ)) (.leaf (3104427043587754:ℤ))))), (.branch 166 (.branch 151 (.leaf (1870575755249636:ℤ)) (.leaf (2283632903964890:ℤ))) (.branch 181 (.leaf (2500979852594537:ℤ)) (.branch 200 (.leaf (2744158847554790:ℤ)) (.leaf (3095142227725925:ℤ))))), (.branch 166 (.branch 151 (.leaf (1876520125006388:ℤ)) (.leaf (2296098117857821:ℤ))) (.branch 181 (.leaf (2517711837711379:ℤ)) (.branch 200 (.leaf (2766301154896034:ℤ)) (.leaf (3126208970844261:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 6 13) 8000 (endpointMeanRuns 6 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 6 13, EndpointRunConditions (endpointMeanCutoff 6 13) (endpointMeanBox 6 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 6 13 h) (endpointMeanCornerA 6 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 6 13, endpointJoint24Q (endpointMeanCornerK 6 13 h) (endpointMeanCornerA 6 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 6 13, endpointRunWeightQ (endpointMeanCutoff 6 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 6 13) = (223858077/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 6 13 h = (logRoundedQ ((endpointMeanCutoff 6 13:ℚ)/200)).2+(223858077/500000000000000:ℚ)+((endpointMeanRuns 6 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 6 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 6 13) r*endpointJoint24Q (endpointMeanCornerK 6 13 h) (endpointMeanCornerA 6 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 6 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 6 13 h≤endpointMeanCorner 6 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 6 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint06_13

namespace EndpointAnalyticJoint07_01
private noncomputable def weights : IntegerLookupTree := (.branch 1326 (.leaf (166667783900000:ℤ)) (.branch 2652 (.leaf (21428712100000:ℤ)) (.leaf (2347656900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 150 (.leaf (1794617249481041:ℤ)) (.branch 200 (.leaf (2134544053027776:ℤ)) (.leaf (2760350574473801:ℤ)))), (.branch 150 (.leaf (1797204215384742:ℤ)) (.branch 200 (.leaf (2139846417135852:ℤ)) (.leaf (2773123881633043:ℤ)))), (.branch 150 (.leaf (1795003028425657:ℤ)) (.branch 200 (.leaf (2135382212740469:ℤ)) (.leaf (2762555926280249:ℤ)))), (.branch 150 (.leaf (1797706704681721:ℤ)) (.branch 200 (.leaf (2140939312454369:ℤ)) (.leaf (2776005813577674:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 7 1) 8000 (endpointMeanRuns 7 1) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 7 1, EndpointRunConditions (endpointMeanCutoff 7 1) (endpointMeanBox 7 1).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 1, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 7 1 h) (endpointMeanCornerA 7 1 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 1, endpointJoint24Q (endpointMeanCornerK 7 1 h) (endpointMeanCornerA 7 1 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 7 1, endpointRunWeightQ (endpointMeanCutoff 7 1) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 7 1) = (461797707/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 7 1 h = (logRoundedQ ((endpointMeanCutoff 7 1:ℚ)/200)).2+(461797707/1000000000000000:ℚ)+((endpointMeanRuns 7 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 7 1).map (fun r => endpointRunWeightQ (endpointMeanCutoff 7 1) r*endpointJoint24Q (endpointMeanCornerK 7 1 h) (endpointMeanCornerA 7 1 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 7 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 7 1 h≤endpointMeanCorner 7 1 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 7 1 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint07_01

namespace EndpointAnalyticJoint07_02
private noncomputable def weights : IntegerLookupTree := (.branch 1326 (.leaf (162998678700000:ℤ)) (.branch 2652 (.leaf (21340414900000:ℤ)) (.leaf (2340076600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 150 (.leaf (1797204215384742:ℤ)) (.branch 200 (.leaf (2139846417135852:ℤ)) (.leaf (2773123881633043:ℤ)))), (.branch 150 (.leaf (1802813257435818:ℤ)) (.branch 200 (.leaf (2151361910082970:ℤ)) (.leaf (2800958443319509:ℤ)))), (.branch 150 (.leaf (1797706704681721:ℤ)) (.branch 200 (.leaf (2140939312454369:ℤ)) (.leaf (2776005813577674:ℤ)))), (.branch 150 (.leaf (1803569396618406:ℤ)) (.branch 200 (.leaf (2153010285541762:ℤ)) (.leaf (2805325865486197:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 7 2) 8000 (endpointMeanRuns 7 2) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 7 2, EndpointRunConditions (endpointMeanCutoff 7 2) (endpointMeanBox 7 2).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 2, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 7 2 h) (endpointMeanCornerA 7 2 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 2, endpointJoint24Q (endpointMeanCornerK 7 2 h) (endpointMeanCornerA 7 2 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 7 2, endpointRunWeightQ (endpointMeanCutoff 7 2) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 7 2) = (460693463/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 7 2 h = (logRoundedQ ((endpointMeanCutoff 7 2:ℚ)/200)).2+(460693463/1000000000000000:ℚ)+((endpointMeanRuns 7 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 7 2).map (fun r => endpointRunWeightQ (endpointMeanCutoff 7 2) r*endpointJoint24Q (endpointMeanCornerK 7 2 h) (endpointMeanCornerA 7 2 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 7 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 7 2 h≤endpointMeanCorner 7 2 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 7 2 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint07_02

namespace EndpointAnalyticJoint07_03
private noncomputable def weights : IntegerLookupTree := (.branch 1722 (.branch 1326 (.leaf (159413597900000:ℤ)) (.leaf (5951373100000:ℤ))) (.branch 2652 (.leaf (5143612800000:ℤ)) (.leaf (2332568300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 177 (.branch 150 (.leaf (1802813257435818:ℤ)) (.leaf (2151361910082970:ℤ))) (.branch 200 (.leaf (2479287535585111:ℤ)) (.leaf (2800958443319509:ℤ)))), (.branch 177 (.branch 150 (.leaf (1808439805206311:ℤ)) (.leaf (2162939373168110:ℤ))) (.branch 200 (.leaf (2498344501573923:ℤ)) (.leaf (2829072387701219:ℤ)))), (.branch 177 (.branch 150 (.leaf (1803569396618406:ℤ)) (.leaf (2153010285541762:ℤ))) (.branch 200 (.leaf (2482130579893909:ℤ)) (.leaf (2805325865486197:ℤ)))), (.branch 177 (.branch 150 (.leaf (1809451208001360:ℤ)) (.leaf (2165149316789619:ℤ))) (.branch 200 (.leaf (2502165094478883:ℤ)) (.leaf (2834955594499755:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 7 3) 8000 (endpointMeanRuns 7 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 7 3, EndpointRunConditions (endpointMeanCutoff 7 3) (endpointMeanBox 7 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 7 3 h) (endpointMeanCornerA 7 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 3, endpointJoint24Q (endpointMeanCornerK 7 3 h) (endpointMeanCornerA 7 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 7 3, endpointRunWeightQ (endpointMeanCutoff 7 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 7 3) = (45959971/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 7 3 h = (logRoundedQ ((endpointMeanCutoff 7 3:ℚ)/200)).2+(45959971/100000000000000:ℚ)+((endpointMeanRuns 7 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 7 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 7 3) r*endpointJoint24Q (endpointMeanCornerK 7 3 h) (endpointMeanCornerA 7 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 7 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 7 3 h≤endpointMeanCorner 7 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 7 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint07_03

namespace EndpointAnalyticJoint07_04
private noncomputable def weights : IntegerLookupTree := (.branch 1722 (.branch 1326 (.leaf (155047216100000:ℤ)) (.leaf (5920175800000:ℤ))) (.branch 2652 (.leaf (5119696200000:ℤ)) (.leaf (2323282100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 177 (.branch 150 (.leaf (1808439805206311:ℤ)) (.leaf (2162939373168110:ℤ))) (.branch 200 (.leaf (2498344501573923:ℤ)) (.leaf (2829072387701219:ℤ)))), (.branch 177 (.branch 150 (.leaf (1814083913331258:ℤ)) (.leaf (2174579139880947:ℤ))) (.branch 200 (.leaf (2517547948334938:ℤ)) (.leaf (2857468519014538:ℤ)))), (.branch 177 (.branch 150 (.leaf (1809451208001360:ℤ)) (.leaf (2165149316789619:ℤ))) (.branch 200 (.leaf (2502165094478883:ℤ)) (.leaf (2834955594499755:ℤ)))), (.branch 177 (.branch 150 (.leaf (1815352201183036:ℤ)) (.leaf (2177356789921207:ℤ))) (.branch 200 (.leaf (2522361317629030:ℤ)) (.leaf (2864898271414384:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 7 4) 8000 (endpointMeanRuns 7 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 7 4, EndpointRunConditions (endpointMeanCutoff 7 4) (endpointMeanBox 7 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 7 4 h) (endpointMeanCornerA 7 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 4, endpointJoint24Q (endpointMeanCornerK 7 4 h) (endpointMeanCornerA 7 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 7 4, endpointRunWeightQ (endpointMeanCutoff 7 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 7 4) = (458246973/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 7 4 h = (logRoundedQ ((endpointMeanCutoff 7 4:ℚ)/200)).2+(458246973/1000000000000000:ℚ)+((endpointMeanRuns 7 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 7 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 7 4) r*endpointJoint24Q (endpointMeanCornerK 7 4 h) (endpointMeanCornerA 7 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 7 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 7 4 h≤endpointMeanCorner 7 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 7 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint07_04

namespace EndpointAnalyticJoint07_05
private noncomputable def weights : IntegerLookupTree := (.branch 1637 (.branch 1326 (.leaf (150804883100000:ℤ)) (.leaf (4577832200000:ℤ))) (.branch 2706 (.leaf (7322756300000:ℤ)) (.leaf (1990870000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 181 (.branch 149 (.leaf (1814083913331258:ℤ)) (.leaf (2162911157082960:ℤ))) (.branch 200 (.leaf (2573283056117434:ℤ)) (.leaf (2857468519014538:ℤ)))), (.branch 181 (.branch 149 (.leaf (1819745636616207:ℤ)) (.leaf (2174385479880419:ℤ))) (.branch 200 (.leaf (2594046586025818:ℤ)) (.leaf (2886149669642689:ℤ)))), (.branch 181 (.branch 149 (.leaf (1815352201183036:ℤ)) (.leaf (2165629992271336:ℤ))) (.branch 200 (.leaf (2578484109383494:ℤ)) (.leaf (2864898271414384:ℤ)))), (.branch 181 (.branch 149 (.leaf (1821272438719225:ℤ)) (.leaf (2177665802485702:ℤ))) (.branch 200 (.leaf (2600339480959714:ℤ)) (.leaf (2895157201572115:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 7 5) 8000 (endpointMeanRuns 7 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 7 5, EndpointRunConditions (endpointMeanCutoff 7 5) (endpointMeanBox 7 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 7 5 h) (endpointMeanCornerA 7 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 5, endpointJoint24Q (endpointMeanCornerK 7 5 h) (endpointMeanCornerA 7 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 7 5, endpointRunWeightQ (endpointMeanCutoff 7 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 7 5) = (456909947/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 7 5 h = (logRoundedQ ((endpointMeanCutoff 7 5:ℚ)/200)).2+(456909947/1000000000000000:ℚ)+((endpointMeanRuns 7 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 7 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 7 5) r*endpointJoint24Q (endpointMeanCornerK 7 5 h) (endpointMeanCornerA 7 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 7 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 7 5 h≤endpointMeanCorner 7 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 7 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint07_05

namespace EndpointAnalyticJoint07_06
private noncomputable def weights : IntegerLookupTree := (.branch 1637 (.branch 1326 (.leaf (147497757200000:ℤ)) (.leaf (4558728600000:ℤ))) (.branch 2706 (.leaf (7295428200000:ℤ)) (.leaf (1984656700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 181 (.branch 149 (.leaf (1819745636616207:ℤ)) (.leaf (2174385479880419:ℤ))) (.branch 200 (.leaf (2594046586025818:ℤ)) (.leaf (2886149669642689:ℤ)))), (.branch 181 (.branch 149 (.leaf (1825425030037763:ℤ)) (.leaf (2185920674379998:ℤ))) (.branch 200 (.leaf (2614977654508409:ℤ)) (.leaf (2915118700398267:ℤ)))), (.branch 181 (.branch 149 (.leaf (1821272438719225:ℤ)) (.leaf (2177665802485702:ℤ))) (.branch 200 (.leaf (2600339480959714:ℤ)) (.leaf (2895157201572115:ℤ)))), (.branch 181 (.branch 149 (.leaf (1827211983369740:ℤ)) (.leaf (2189768503502296:ℤ))) (.branch 200 (.leaf (2622380099854303:ℤ)) (.leaf (2925735725225862:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 7 6) 8000 (endpointMeanRuns 7 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 7 6, EndpointRunConditions (endpointMeanCutoff 7 6) (endpointMeanBox 7 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 7 6 h) (endpointMeanCornerA 7 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 6, endpointJoint24Q (endpointMeanCornerK 7 6 h) (endpointMeanCornerA 7 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 7 6, endpointRunWeightQ (endpointMeanCutoff 7 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 7 6) = (113962849/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 7 6 h = (logRoundedQ ((endpointMeanCutoff 7 6:ℚ)/200)).2+(113962849/250000000000000:ℚ)+((endpointMeanRuns 7 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 7 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 7 6) r*endpointJoint24Q (endpointMeanCornerK 7 6 h) (endpointMeanCornerA 7 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 7 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 7 6 h≤endpointMeanCorner 7 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 7 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint07_06

namespace EndpointAnalyticJoint07_07
private noncomputable def weights : IntegerLookupTree := (.branch 1637 (.branch 1326 (.leaf (143469164700000:ℤ)) (.leaf (4535093500000:ℤ))) (.branch 2040 (.leaf (2756769400000:ℤ)) (.branch 2706 (.leaf (1622344700000:ℤ)) (.leaf (1976969600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 149 (.leaf (1825425030037763:ℤ)) (.leaf (2185920674379998:ℤ))) (.branch 181 (.leaf (2389473293633032:ℤ)) (.branch 200 (.leaf (2614977654508409:ℤ)) (.leaf (2915118700398267:ℤ))))), (.branch 165 (.branch 149 (.leaf (1831122148744095:ℤ)) (.leaf (2197517063508300:ℤ))) (.branch 181 (.leaf (2405252323325486:ℤ)) (.branch 200 (.leaf (2636077613415022:ℤ)) (.leaf (2944378500808566:ℤ))))), (.branch 165 (.branch 149 (.leaf (1827211983369740:ℤ)) (.leaf (2189768503502296:ℤ))) (.branch 181 (.leaf (2394856071096515:ℤ)) (.branch 200 (.leaf (2622380099854303:ℤ)) (.leaf (2925735725225862:ℤ))))), (.branch 165 (.branch 149 (.leaf (1833170898099057:ℤ)) (.leaf (2201938467076689:ℤ))) (.branch 181 (.leaf (2411445688176033:ℤ)) (.branch 200 (.leaf (2644607536233620:ℤ)) (.leaf (2956637217908140:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 7 7) 8000 (endpointMeanRuns 7 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 7 7, EndpointRunConditions (endpointMeanCutoff 7 7) (endpointMeanBox 7 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 7 7 h) (endpointMeanCornerA 7 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 7, endpointJoint24Q (endpointMeanCornerK 7 7 h) (endpointMeanCornerA 7 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 7 7, endpointRunWeightQ (endpointMeanCutoff 7 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 7 7) = (1818167/4000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 7 7 h = (logRoundedQ ((endpointMeanCutoff 7 7:ℚ)/200)).2+(1818167/4000000000000:ℚ)+((endpointMeanRuns 7 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 7 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 7 7) r*endpointJoint24Q (endpointMeanCornerK 7 7 h) (endpointMeanCornerA 7 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 7 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 7 7 h≤endpointMeanCorner 7 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 7 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint07_07

namespace EndpointAnalyticJoint07_08
private noncomputable def weights : IntegerLookupTree := (.branch 1637 (.branch 1326 (.leaf (139554247300000:ℤ)) (.leaf (4511724300000:ℤ))) (.branch 2040 (.leaf (2743813600000:ℤ)) (.branch 2706 (.leaf (1615387900000:ℤ)) (.leaf (1969368900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 149 (.leaf (1831122148744095:ℤ)) (.leaf (2197517063508300:ℤ))) (.branch 181 (.leaf (2405252323325486:ℤ)) (.branch 200 (.leaf (2636077613415022:ℤ)) (.leaf (2944378500808566:ℤ))))), (.branch 165 (.branch 149 (.leaf (1836837048055503:ℤ)) (.leaf (2209174971905068:ℤ))) (.branch 181 (.leaf (2421135550783487:ℤ)) (.branch 200 (.leaf (2657347825503370:ℤ)) (.leaf (2973931989403816:ℤ))))), (.branch 165 (.branch 149 (.leaf (1833170898099057:ℤ)) (.leaf (2201938467076689:ℤ))) (.branch 181 (.leaf (2411445688176033:ℤ)) (.branch 200 (.leaf (2644607536233620:ℤ)) (.leaf (2956637217908140:ℤ))))), (.branch 165 (.branch 149 (.leaf (1839149246076992:ℤ)) (.leaf (2214176067030523:ℤ))) (.branch 181 (.leaf (2428150224643883:ℤ)) (.branch 200 (.leaf (2667023373572822:ℤ)) (.leaf (2987865090803701:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 7 8) 8000 (endpointMeanRuns 7 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 7 8, EndpointRunConditions (endpointMeanCutoff 7 8) (endpointMeanBox 7 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 7 8 h) (endpointMeanCornerA 7 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 8, endpointJoint24Q (endpointMeanCornerK 7 8 h) (endpointMeanCornerA 7 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 7 8, endpointRunWeightQ (endpointMeanCutoff 7 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 7 8) = (453246837/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 7 8 h = (logRoundedQ ((endpointMeanCutoff 7 8:ℚ)/200)).2+(453246837/1000000000000000:ℚ)+((endpointMeanRuns 7 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 7 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 7 8) r*endpointJoint24Q (endpointMeanCornerK 7 8 h) (endpointMeanCornerA 7 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 7 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 7 8 h≤endpointMeanCorner 7 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 7 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint07_08

namespace EndpointAnalyticJoint07_09
private noncomputable def weights : IntegerLookupTree := (.branch 1722 (.branch 1326 (.leaf (135749543300000:ℤ)) (.branch 1542 (.leaf (3077036000000:ℤ)) (.leaf (1542978500000:ℤ)))) (.branch 2652 (.branch 2139 (.leaf (2288709000000:ℤ)) (.leaf (988104100000:ℤ))) (.branch 3900 (.leaf (585530600000:ℤ)) (.leaf (68574900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 134 (.leaf (1836837048055503:ℤ)) (.branch 150 (.leaf (2029947059706314:ℤ)) (.leaf (2221767975819080:ℤ)))) (.branch 186 (.branch 177 (.leaf (2379637254508952:ℤ)) (.leaf (2595849191713117:ℤ))) (.branch 200 (.leaf (2736645349756798:ℤ)) (.leaf (2973931989403816:ℤ))))), (.branch 162 (.branch 134 (.leaf (1842569783464934:ℤ)) (.branch 150 (.leaf (2038538267085190:ℤ)) (.leaf (2233724326167775:ℤ)))) (.branch 186 (.branch 177 (.leaf (2394742296480895:ℤ)) (.leaf (2615802105220952:ℤ))) (.branch 200 (.leaf (2760077384245965:ℤ)) (.leaf (3003782114008306:ℤ))))), (.branch 162 (.branch 134 (.leaf (1839149246076992:ℤ)) (.branch 150 (.leaf (2033519860496594:ℤ)) (.leaf (2226878851729186:ℤ)))) (.branch 186 (.branch 177 (.leaf (2386229903504505:ℤ)) (.leaf (2604789559030352:ℤ))) (.branch 200 (.leaf (2747312967135190:ℤ)) (.leaf (2987865090803701:ℤ))))), (.branch 162 (.branch 134 (.leaf (1845147090679372:ℤ)) (.branch 150 (.leaf (2042525236372281:ℤ)) (.leaf (2239434366279148:ℤ)))) (.branch 186 (.branch 177 (.leaf (2402115093094620:ℤ)) (.leaf (2625814115447285:ℤ))) (.branch 200 (.leaf (2772034366691250:ℤ)) (.leaf (3019422791126066:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 7 9) 8000 (endpointMeanRuns 7 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 7 9, EndpointRunConditions (endpointMeanCutoff 7 9) (endpointMeanBox 7 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 7 9 h) (endpointMeanCornerA 7 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 9, endpointJoint24Q (endpointMeanCornerK 7 9 h) (endpointMeanCornerA 7 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 7 9, endpointRunWeightQ (endpointMeanCutoff 7 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 7 9) = (451966327/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 7 9 h = (logRoundedQ ((endpointMeanCutoff 7 9:ℚ)/200)).2+(451966327/1000000000000000:ℚ)+((endpointMeanRuns 7 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 7 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 7 9) r*endpointJoint24Q (endpointMeanCornerK 7 9 h) (endpointMeanCornerA 7 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 7 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 7 9 h≤endpointMeanCorner 7 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 7 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint07_09

namespace EndpointAnalyticJoint07_10
private noncomputable def weights : IntegerLookupTree := (.branch 2139 (.branch 1326 (.leaf (132782883700000:ℤ)) (.branch 1722 (.leaf (5751937900000:ℤ)) (.leaf (2280376700000:ℤ)))) (.branch 2652 (.leaf (984797200000:ℤ)) (.branch 3900 (.leaf (583730300000:ℤ)) (.leaf (68388300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 134 (.leaf (1842569783464934:ℤ)) (.branch 150 (.leaf (2038538267085190:ℤ)) (.leaf (2233724326167775:ℤ)))) (.branch 177 (.leaf (2394742296480895:ℤ)) (.branch 200 (.leaf (2615802105220952:ℤ)) (.leaf (3003782114008306:ℤ))))), (.branch 162 (.branch 134 (.leaf (1848320410638532:ℤ)) (.branch 150 (.leaf (2047165834448859:ℤ)) (.leaf (2245745019109944:ℤ)))) (.branch 177 (.leaf (2409943219576119:ℤ)) (.branch 200 (.leaf (2635908386173521:ℤ)) (.leaf (3033931852034371:ℤ))))), (.branch 162 (.branch 134 (.leaf (1845147090679372:ℤ)) (.branch 150 (.leaf (2042525236372281:ℤ)) (.leaf (2239434366279148:ℤ)))) (.branch 177 (.leaf (2402115093094620:ℤ)) (.branch 200 (.leaf (2625814115447285:ℤ)) (.leaf (3019422791126066:ℤ))))), (.branch 162 (.branch 134 (.leaf (1851164495488706:ℤ)) (.branch 150 (.leaf (2051570492259096:ℤ)) (.leaf (2252060670915195:ℤ)))) (.branch 177 (.leaf (2418106030772105:ℤ)) (.branch 200 (.leaf (2647008371551088:ℤ)) (.leaf (3051313802498079:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 7 10) 8000 (endpointMeanRuns 7 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 7 10, EndpointRunConditions (endpointMeanCutoff 7 10) (endpointMeanBox 7 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 7 10 h) (endpointMeanCornerA 7 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 10, endpointJoint24Q (endpointMeanCornerK 7 10 h) (endpointMeanCornerA 7 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 7 10, endpointRunWeightQ (endpointMeanCutoff 7 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 7 10) = (225476039/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 7 10 h = (logRoundedQ ((endpointMeanCutoff 7 10:ℚ)/200)).2+(225476039/500000000000000:ℚ)+((endpointMeanRuns 7 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 7 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 7 10) r*endpointJoint24Q (endpointMeanCornerK 7 10 h) (endpointMeanCornerA 7 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 7 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 7 10 h≤endpointMeanCorner 7 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 7 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint07_10

namespace EndpointAnalyticJoint07_11
private noncomputable def weights : IntegerLookupTree := (.branch 2040 (.branch 1326 (.leaf (129168218200000:ℤ)) (.branch 1637 (.leaf (4447655300000:ℤ)) (.leaf (2708293900000:ℤ)))) (.branch 2706 (.leaf (1596315000000:ℤ)) (.branch 4018 (.leaf (528127800000:ℤ)) (.leaf (48828300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 133 (.leaf (1848320410638532:ℤ)) (.branch 149 (.leaf (2035467841722731:ℤ)) (.leaf (2232676653683246:ℤ)))) (.branch 181 (.leaf (2453217355844578:ℤ)) (.branch 200 (.leaf (2700404515324614:ℤ)) (.leaf (3033931852034371:ℤ))))), (.branch 165 (.branch 133 (.leaf (1854088985416171:ℤ)) (.branch 149 (.leaf (2043946649646316:ℤ)) (.leaf (2244521084991862:ℤ)))) (.branch 181 (.leaf (2469417323261272:ℤ)) (.branch 200 (.leaf (2722193773908269:ℤ)) (.leaf (3064384210779436:ℤ))))), (.branch 165 (.branch 133 (.leaf (1851164495488706:ℤ)) (.branch 149 (.leaf (2039770934272263:ℤ)) (.leaf (2238855681762530:ℤ)))) (.branch 181 (.leaf (2461907245531719:ℤ)) (.branch 200 (.leaf (2712426652253403:ℤ)) (.leaf (3051313802498079:ℤ))))), (.branch 165 (.branch 133 (.leaf (1857201524294864:ℤ)) (.branch 149 (.leaf (2048660939295148:ℤ)) (.leaf (2251298454618103:ℤ)))) (.branch 181 (.leaf (2478961338669749:ℤ)) (.branch 200 (.leaf (2735417328109231:ℤ)) (.leaf (3083541645336467:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 7 11) 8000 (endpointMeanRuns 7 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 7 11, EndpointRunConditions (endpointMeanCutoff 7 11) (endpointMeanBox 7 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 7 11 h) (endpointMeanCornerA 7 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 11, endpointJoint24Q (endpointMeanCornerK 7 11 h) (endpointMeanCornerA 7 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 7 11, endpointRunWeightQ (endpointMeanCutoff 7 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 7 11) = (7026511/15625000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 7 11 h = (logRoundedQ ((endpointMeanCutoff 7 11:ℚ)/200)).2+(7026511/15625000000000:ℚ)+((endpointMeanRuns 7 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 7 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 7 11) r*endpointJoint24Q (endpointMeanCornerK 7 11 h) (endpointMeanCornerA 7 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 7 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 7 11 h≤endpointMeanCorner 7 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 7 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint07_11

namespace EndpointAnalyticJoint07_12
private noncomputable def weights : IntegerLookupTree := (.branch 2040 (.branch 1326 (.leaf (125654692800000:ℤ)) (.branch 1637 (.leaf (4425244100000:ℤ)) (.leaf (2695869200000:ℤ)))) (.branch 2706 (.leaf (1589643400000:ℤ)) (.branch 4018 (.leaf (526139700000:ℤ)) (.leaf (48665900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 133 (.leaf (1854088985416171:ℤ)) (.branch 149 (.leaf (2043946649646316:ℤ)) (.leaf (2244521084991862:ℤ)))) (.branch 181 (.leaf (2469417323261272:ℤ)) (.branch 200 (.leaf (2722193773908269:ℤ)) (.leaf (3064384210779436:ℤ))))), (.branch 165 (.branch 133 (.leaf (1859875563811998:ℤ)) (.branch 149 (.leaf (2052460776321848:ℤ)) (.leaf (2256428351441787:ℤ)))) (.branch 181 (.leaf (2485724268130931:ℤ)) (.branch 200 (.leaf (2744158847554790:ℤ)) (.leaf (3095142227725925:ℤ))))), (.branch 165 (.branch 133 (.leaf (1857201524294864:ℤ)) (.branch 149 (.leaf (2048660939295148:ℤ)) (.leaf (2251298454618103:ℤ)))) (.branch 181 (.leaf (2478961338669749:ℤ)) (.branch 200 (.leaf (2735417328109231:ℤ)) (.leaf (3083541645336467:ℤ))))), (.branch 165 (.branch 133 (.leaf (1863258241095736:ℤ)) (.branch 149 (.leaf (2057589689937937:ℤ)) (.leaf (2263810380031204:ℤ)))) (.branch 181 (.leaf (2496133568708868:ℤ)) (.branch 200 (.leaf (2758602874184264:ℤ)) (.leaf (3116109877240431:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 7 12) 8000 (endpointMeanRuns 7 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 7 12, EndpointRunConditions (endpointMeanCutoff 7 12) (endpointMeanBox 7 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 7 12 h) (endpointMeanCornerA 7 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 12, endpointJoint24Q (endpointMeanCornerK 7 12 h) (endpointMeanCornerA 7 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 7 12, endpointRunWeightQ (endpointMeanCutoff 7 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 7 12) = (448454873/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 7 12 h = (logRoundedQ ((endpointMeanCutoff 7 12:ℚ)/200)).2+(448454873/1000000000000000:ℚ)+((endpointMeanRuns 7 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 7 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 7 12) r*endpointJoint24Q (endpointMeanCornerK 7 12 h) (endpointMeanCornerA 7 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 7 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 7 12 h≤endpointMeanCorner 7 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 7 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint07_12

namespace EndpointAnalyticJoint07_13
private noncomputable def weights : IntegerLookupTree := (.branch 2040 (.branch 1326 (.leaf (122914651500000:ℤ)) (.branch 1637 (.leaf (4407487600000:ℤ)) (.leaf (2686025100000:ℤ)))) (.branch 2706 (.leaf (1584357400000:ℤ)) (.branch 4018 (.leaf (524564600000:ℤ)) (.leaf (48537300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 133 (.leaf (1859875563811998:ℤ)) (.branch 149 (.leaf (2052460776321848:ℤ)) (.leaf (2256428351441787:ℤ)))) (.branch 181 (.leaf (2485724268130931:ℤ)) (.branch 200 (.leaf (2744158847554790:ℤ)) (.leaf (3095142227725925:ℤ))))), (.branch 165 (.branch 133 (.leaf (1865680202014984:ℤ)) (.branch 149 (.leaf (2061010368870745:ℤ)) (.leaf (2268398786375744:ℤ)))) (.branch 181 (.leaf (2502138896885557:ℤ)) (.branch 200 (.leaf (2766301154896034:ℤ)) (.leaf (3126208970844261:ℤ))))), (.branch 165 (.branch 133 (.leaf (1863258241095736:ℤ)) (.branch 149 (.leaf (2057589689937937:ℤ)) (.leaf (2263810380031204:ℤ)))) (.branch 181 (.leaf (2496133568708868:ℤ)) (.branch 200 (.leaf (2758602874184264:ℤ)) (.leaf (3116109877240431:ℤ))))), (.branch 165 (.branch 133 (.leaf (1869334710097930:ℤ)) (.branch 149 (.leaf (2066557355067019:ℤ)) (.leaf (2276391842327446:ℤ)))) (.branch 181 (.leaf (2513424754005545:ℤ)) (.branch 200 (.leaf (2781984942209082:ℤ)) (.leaf (3149022093384386:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 7 13) 8000 (endpointMeanRuns 7 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 7 13, EndpointRunConditions (endpointMeanCutoff 7 13) (endpointMeanBox 7 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 7 13 h) (endpointMeanCornerA 7 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 13, endpointJoint24Q (endpointMeanCornerK 7 13 h) (endpointMeanCornerA 7 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 7 13, endpointRunWeightQ (endpointMeanCutoff 7 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 7 13) = (111867741/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 7 13 h = (logRoundedQ ((endpointMeanCutoff 7 13:ℚ)/200)).2+(111867741/250000000000000:ℚ)+((endpointMeanRuns 7 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 7 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 7 13) r*endpointJoint24Q (endpointMeanCornerK 7 13 h) (endpointMeanCornerA 7 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 7 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 7 13 h≤endpointMeanCorner 7 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 7 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint07_13

namespace EndpointAnalyticJoint07_14
private noncomputable def weights : IntegerLookupTree := (.branch 2139 (.branch 1326 (.leaf (119575603200000:ℤ)) (.branch 1722 (.leaf (5643561000000:ℤ)) (.leaf (2241770600000:ℤ)))) (.branch 2652 (.leaf (969475600000:ℤ)) (.branch 3900 (.leaf (575389100000:ℤ)) (.leaf (67523300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 162 (.branch 134 (.leaf (1865680202014984:ℤ)) (.branch 150 (.leaf (2073268238546753:ℤ)) (.leaf (2282196625393602:ℤ)))) (.branch 177 (.leaf (2456127381115355:ℤ)) (.branch 200 (.leaf (2697159267616018:ℤ)) (.leaf (3126208970844261:ℤ))))), (.branch 162 (.branch 134 (.leaf (1871502956389462:ℤ)) (.branch 150 (.leaf (2082042791215120:ℤ)) (.leaf (2294478169962970:ℤ)))) (.branch 177 (.leaf (2471717953632188:ℤ)) (.branch 200 (.leaf (2717890897849162:ℤ)) (.leaf (3157587538898900:ℤ))))), (.branch 162 (.branch 134 (.leaf (1869334710097930:ℤ)) (.branch 150 (.leaf (2078947309973447:ℤ)) (.leaf (2290368327867408:ℤ)))) (.branch 177 (.leaf (2466720395467094:ℤ)) (.branch 200 (.leaf (2711623090660455:ℤ)) (.leaf (3149022093384386:ℤ))))), (.branch 162 (.branch 134 (.leaf (1875430995717446:ℤ)) (.branch 150 (.leaf (2088153859816285:ℤ)) (.leaf (2303281806677886:ℤ)))) (.branch 177 (.leaf (2483141412189016:ℤ)) (.branch 200 (.leaf (2733509953825048:ℤ)) (.leaf (3182281926914820:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 7 14) 8000 (endpointMeanRuns 7 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 7 14, EndpointRunConditions (endpointMeanCutoff 7 14) (endpointMeanBox 7 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 7 14 h) (endpointMeanCornerA 7 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 7 14, endpointJoint24Q (endpointMeanCornerK 7 14 h) (endpointMeanCornerA 7 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 7 14, endpointRunWeightQ (endpointMeanCutoff 7 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 7 14) = (111563197/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 7 14 h = (logRoundedQ ((endpointMeanCutoff 7 14:ℚ)/200)).2+(111563197/250000000000000:ℚ)+((endpointMeanRuns 7 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 7 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 7 14) r*endpointJoint24Q (endpointMeanCornerK 7 14 h) (endpointMeanCornerA 7 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 7 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 7 14 h≤endpointMeanCorner 7 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 7 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint07_14

namespace EndpointAnalyticJoint08_01
private noncomputable def weights : IntegerLookupTree := (.branch 1281 (.leaf (165025873400000:ℤ)) (.branch 2561 (.leaf (24980317100000:ℤ)) (.leaf (3022062700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 150 (.leaf (1796039329816255:ℤ)) (.branch 200 (.leaf (2137511494152839:ℤ)) (.leaf (2767705852273894:ℤ)))), (.branch 150 (.leaf (1797706704681721:ℤ)) (.branch 200 (.leaf (2140939312454369:ℤ)) (.leaf (2776005813577674:ℤ)))), (.branch 150 (.leaf (1796479536850982:ℤ)) (.branch 200 (.leaf (2138475531817413:ℤ)) (.leaf (2770275764235038:ℤ)))), (.branch 150 (.leaf (1798220552703807:ℤ)) (.branch 200 (.leaf (2142065399711435:ℤ)) (.leaf (2779012014842198:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 8 1) 8000 (endpointMeanRuns 8 1) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 8 1, EndpointRunConditions (endpointMeanCutoff 8 1) (endpointMeanBox 8 1).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 1, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 8 1 h) (endpointMeanCornerA 8 1 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 1, endpointJoint24Q (endpointMeanCornerK 8 1 h) (endpointMeanCornerA 8 1 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 8 1, endpointRunWeightQ (endpointMeanCutoff 8 1) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 8 1) = (461520651/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 8 1 h = (logRoundedQ ((endpointMeanCutoff 8 1:ℚ)/200)).2+(461520651/1000000000000000:ℚ)+((endpointMeanRuns 8 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 8 1).map (fun r => endpointRunWeightQ (endpointMeanCutoff 8 1) r*endpointJoint24Q (endpointMeanCornerK 8 1 h) (endpointMeanCornerA 8 1 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 8 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 8 1 h≤endpointMeanCorner 8 1 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 8 1 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint08_01

namespace EndpointAnalyticJoint08_02
private noncomputable def weights : IntegerLookupTree := (.branch 1281 (.leaf (162284444500000:ℤ)) (.branch 2561 (.leaf (24902117700000:ℤ)) (.leaf (3014669400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 150 (.leaf (1797706704681721:ℤ)) (.branch 200 (.leaf (2140939312454369:ℤ)) (.leaf (2776005813577674:ℤ)))), (.branch 150 (.leaf (1803569396618406:ℤ)) (.branch 200 (.leaf (2153010285541762:ℤ)) (.leaf (2805325865486197:ℤ)))), (.branch 150 (.leaf (1798220552703807:ℤ)) (.branch 200 (.leaf (2142065399711435:ℤ)) (.leaf (2779012014842198:ℤ)))), (.branch 150 (.leaf (1804342737553389:ℤ)) (.branch 200 (.leaf (2154709163373346:ℤ)) (.leaf (2809884027910772:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 8 2) 8000 (endpointMeanRuns 8 2) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 8 2, EndpointRunConditions (endpointMeanCutoff 8 2) (endpointMeanBox 8 2).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 2, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 8 2 h) (endpointMeanCornerA 8 2 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 2, endpointJoint24Q (endpointMeanCornerK 8 2 h) (endpointMeanCornerA 8 2 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 8 2, endpointRunWeightQ (endpointMeanCutoff 8 2) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 8 2) = (460693463/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 8 2 h = (logRoundedQ ((endpointMeanCutoff 8 2:ℚ)/200)).2+(460693463/1000000000000000:ℚ)+((endpointMeanRuns 8 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 8 2).map (fun r => endpointRunWeightQ (endpointMeanCutoff 8 2) r*endpointJoint24Q (endpointMeanCornerK 8 2 h) (endpointMeanCornerA 8 2 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 8 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 8 2 h≤endpointMeanCorner 8 2 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 8 2 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint08_02

namespace EndpointAnalyticJoint08_03
private noncomputable def weights : IntegerLookupTree := (.branch 1940 (.branch 1281 (.leaf (157819946500000:ℤ)) (.leaf (12453389500000:ℤ))) (.branch 2561 (.leaf (2188390600000:ℤ)) (.leaf (3002464100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 150 (.leaf (1803569396618406:ℤ)) (.leaf (2153010285541762:ℤ))) (.branch 200 (.leaf (2341946380957299:ℤ)) (.leaf (2805325865486197:ℤ)))), (.branch 166 (.branch 150 (.leaf (1809451208001360:ℤ)) (.leaf (2165149316789619:ℤ))) (.branch 200 (.leaf (2358383658234356:ℤ)) (.leaf (2834955594499755:ℤ)))), (.branch 166 (.branch 150 (.leaf (1804342737553389:ℤ)) (.leaf (2154709163373346:ℤ))) (.branch 200 (.leaf (2344316587950007:ℤ)) (.leaf (2809884027910772:ℤ)))), (.branch 166 (.branch 150 (.leaf (1810485765868069:ℤ)) (.leaf (2167427558164428:ℤ))) (.branch 200 (.leaf (2361566651751722:ℤ)) (.leaf (2841098997823651:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 8 3) 8000 (endpointMeanRuns 8 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 8 3, EndpointRunConditions (endpointMeanCutoff 8 3) (endpointMeanBox 8 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 8 3 h) (endpointMeanCornerA 8 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 3, endpointJoint24Q (endpointMeanCornerK 8 3 h) (endpointMeanCornerA 8 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 8 3, endpointRunWeightQ (endpointMeanCutoff 8 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 8 3) = (28707993/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 8 3 h = (logRoundedQ ((endpointMeanCutoff 8 3:ℚ)/200)).2+(28707993/62500000000000:ℚ)+((endpointMeanRuns 8 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 8 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 8 3) r*endpointJoint24Q (endpointMeanCornerK 8 3 h) (endpointMeanCornerA 8 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 8 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 8 3 h≤endpointMeanCorner 8 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 8 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint08_03

namespace EndpointAnalyticJoint08_04
private noncomputable def weights : IntegerLookupTree := (.branch 1940 (.branch 1281 (.leaf (153482611800000:ℤ)) (.leaf (12388247400000:ℤ))) (.branch 2561 (.leaf (2178581700000:ℤ)) (.leaf (2990402000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 150 (.leaf (1809451208001360:ℤ)) (.leaf (2165149316789619:ℤ))) (.branch 200 (.leaf (2358383658234356:ℤ)) (.leaf (2834955594499755:ℤ)))), (.branch 166 (.branch 150 (.leaf (1815352201183036:ℤ)) (.leaf (2177356789921207:ℤ))) (.branch 200 (.leaf (2374936302834290:ℤ)) (.leaf (2864898271414384:ℤ)))), (.branch 166 (.branch 150 (.leaf (1810485765868069:ℤ)) (.leaf (2167427558164428:ℤ))) (.branch 200 (.leaf (2361566651751722:ℤ)) (.leaf (2841098997823651:ℤ)))), (.branch 166 (.branch 150 (.leaf (1816649708611085:ℤ)) (.leaf (2180221024602682:ℤ))) (.branch 200 (.leaf (2378943645807943:ℤ)) (.leaf (2872660734484549:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 8 4) 8000 (endpointMeanRuns 8 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 8 4, EndpointRunConditions (endpointMeanCutoff 8 4) (endpointMeanBox 8 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 8 4 h) (endpointMeanCornerA 8 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 4, endpointJoint24Q (endpointMeanCornerK 8 4 h) (endpointMeanCornerA 8 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 8 4, endpointRunWeightQ (endpointMeanCutoff 8 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 8 4) = (228989161/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 8 4 h = (logRoundedQ ((endpointMeanCutoff 8 4:ℚ)/200)).2+(228989161/500000000000000:ℚ)+((endpointMeanRuns 8 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 8 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 8 4) r*endpointJoint24Q (endpointMeanCornerK 8 4 h) (endpointMeanCornerA 8 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 8 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 8 4 h≤endpointMeanCorner 8 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 8 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint08_04

namespace EndpointAnalyticJoint08_05
private noncomputable def weights : IntegerLookupTree := (.branch 1940 (.branch 1281 (.leaf (150101652000000:ℤ)) (.leaf (12336678000000:ℤ))) (.branch 2561 (.leaf (2170816600000:ℤ)) (.leaf (2980853000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 150 (.leaf (1815352201183036:ℤ)) (.leaf (2177356789921207:ℤ))) (.branch 200 (.leaf (2374936302834290:ℤ)) (.leaf (2864898271414384:ℤ)))), (.branch 166 (.branch 150 (.leaf (1821272438719225:ℤ)) (.leaf (2189633090823294:ℤ))) (.branch 200 (.leaf (2391605124478739:ℤ)) (.leaf (2895157201572115:ℤ)))), (.branch 166 (.branch 150 (.leaf (1816649708611085:ℤ)) (.leaf (2180221024602682:ℤ))) (.branch 200 (.leaf (2378943645807943:ℤ)) (.leaf (2872660734484549:ℤ)))), (.branch 166 (.branch 150 (.leaf (1822834636987269:ℤ)) (.leaf (2193090005806303:ℤ))) (.branch 200 (.leaf (2396448504103021:ℤ)) (.leaf (2904573090121350:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 8 5) 8000 (endpointMeanRuns 8 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 8 5, EndpointRunConditions (endpointMeanCutoff 8 5) (endpointMeanBox 8 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 8 5 h) (endpointMeanCornerA 8 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 5, endpointJoint24Q (endpointMeanCornerK 8 5 h) (endpointMeanCornerA 8 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 8 5, endpointRunWeightQ (endpointMeanCutoff 8 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 8 5) = (456909947/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 8 5 h = (logRoundedQ ((endpointMeanCutoff 8 5:ℚ)/200)).2+(456909947/1000000000000000:ℚ)+((endpointMeanRuns 8 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 8 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 8 5) r*endpointJoint24Q (endpointMeanCornerK 8 5 h) (endpointMeanCornerA 8 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 8 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 8 5 h≤endpointMeanCorner 8 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 8 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint08_05

namespace EndpointAnalyticJoint08_06
private noncomputable def weights : IntegerLookupTree := (.branch 1439 (.branch 1281 (.leaf (145983386800000:ℤ)) (.leaf (2793883900000:ℤ))) (.branch 1940 (.leaf (6199000100000:ℤ)) (.branch 2561 (.leaf (2161210500000:ℤ)) (.leaf (2969040100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 150 (.leaf (1821272438719225:ℤ)) (.leaf (2189633090823294:ℤ))) (.branch 189 (.leaf (2391605124478739:ℤ)) (.branch 200 (.leaf (2720092097084293:ℤ)) (.leaf (2895157201572115:ℤ))))), (.branch 166 (.branch 150 (.leaf (1827211983369740:ℤ)) (.leaf (2201978607558323:ℤ))) (.branch 189 (.leaf (2408390938572494:ℤ)) (.branch 200 (.leaf (2745445514389701:ℤ)) (.leaf (2925735725225862:ℤ))))), (.branch 166 (.branch 150 (.leaf (1822834636987269:ℤ)) (.leaf (2193090005806303:ℤ))) (.branch 189 (.leaf (2396448504103021:ℤ)) (.branch 200 (.leaf (2727734975374200:ℤ)) (.leaf (2904573090121350:ℤ))))), (.branch 166 (.branch 150 (.leaf (1829040622443878:ℤ)) (.leaf (2206034947509039:ℤ))) (.branch 189 (.leaf (2414082167493782:ℤ)) (.branch 200 (.leaf (2754447422019409:ℤ)) (.leaf (2936839959756291:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 8 6) 8000 (endpointMeanRuns 8 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 8 6, EndpointRunConditions (endpointMeanCutoff 8 6) (endpointMeanBox 8 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 8 6 h) (endpointMeanCornerA 8 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 6, endpointJoint24Q (endpointMeanCornerK 8 6 h) (endpointMeanCornerA 8 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 8 6, endpointRunWeightQ (endpointMeanCutoff 8 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 8 6) = (28474267/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 8 6 h = (logRoundedQ ((endpointMeanCutoff 8 6:ℚ)/200)).2+(28474267/62500000000000:ℚ)+((endpointMeanRuns 8 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 8 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 8 6) r*endpointJoint24Q (endpointMeanCornerK 8 6 h) (endpointMeanCornerA 8 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 8 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 8 6 h≤endpointMeanCorner 8 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 8 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint08_06

namespace EndpointAnalyticJoint08_07
private noncomputable def weights : IntegerLookupTree := (.branch 1439 (.branch 1281 (.leaf (141981612200000:ℤ)) (.leaf (2778957000000:ℤ))) (.branch 1940 (.leaf (6168366300000:ℤ)) (.branch 2561 (.leaf (2151713400000:ℤ)) (.leaf (2957361300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 150 (.leaf (1827211983369740:ℤ)) (.leaf (2201978607558323:ℤ))) (.branch 189 (.leaf (2408390938572494:ℤ)) (.branch 200 (.leaf (2745445514389701:ℤ)) (.leaf (2925735725225862:ℤ))))), (.branch 166 (.branch 150 (.leaf (1833170898099057:ℤ)) (.leaf (2214393730376717:ℤ))) (.branch 189 (.leaf (2425294566243375:ℤ)) (.branch 200 (.leaf (2771035245667618:ℤ)) (.leaf (2956637217908140:ℤ))))), (.branch 166 (.branch 150 (.leaf (1829040622443878:ℤ)) (.leaf (2206034947509039:ℤ))) (.branch 189 (.leaf (2414082167493782:ℤ)) (.branch 200 (.leaf (2754447422019409:ℤ)) (.leaf (2936839959756291:ℤ))))), (.branch 166 (.branch 150 (.leaf (1835267736671417:ℤ)) (.leaf (2219056298075639:ℤ))) (.branch 189 (.leaf (2431845583760126:ℤ)) (.branch 200 (.leaf (2781421461089177:ℤ)) (.leaf (2969465281681373:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 8 7) 8000 (endpointMeanRuns 8 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 8 7, EndpointRunConditions (endpointMeanCutoff 8 7) (endpointMeanBox 8 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 8 7 h) (endpointMeanCornerA 8 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 7, endpointJoint24Q (endpointMeanCornerK 8 7 h) (endpointMeanCornerA 8 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 8 7, endpointRunWeightQ (endpointMeanCutoff 8 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 8 7) = (141963/312500000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 8 7 h = (logRoundedQ ((endpointMeanCutoff 8 7:ℚ)/200)).2+(141963/312500000000:ℚ)+((endpointMeanRuns 8 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 8 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 8 7) r*endpointJoint24Q (endpointMeanCornerK 8 7 h) (endpointMeanCornerA 8 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 8 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 8 7 h≤endpointMeanCorner 8 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 8 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint08_07

namespace EndpointAnalyticJoint08_08
private noncomputable def weights : IntegerLookupTree := (.branch 1940 (.branch 1281 (.leaf (138092767900000:ℤ)) (.branch 1439 (.leaf (2764197600000:ℤ)) (.leaf (6138076300000:ℤ)))) (.branch 2561 (.leaf (2142322900000:ℤ)) (.branch 3765 (.leaf (785739600000:ℤ)) (.leaf (100683400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 134 (.leaf (1833170898099057:ℤ)) (.branch 150 (.leaf (2024554188803366:ℤ)) (.leaf (2214393730376717:ℤ)))) (.branch 189 (.leaf (2425294566243375:ℤ)) (.branch 200 (.leaf (2771035245667618:ℤ)) (.leaf (2956637217908140:ℤ))))), (.branch 166 (.branch 134 (.leaf (1839149246076992:ℤ)) (.branch 150 (.leaf (2033519860496594:ℤ)) (.leaf (2226878851729186:ℤ)))) (.branch 189 (.leaf (2442316834382404:ℤ)) (.branch 200 (.leaf (2796863493551838:ℤ)) (.leaf (2987865090803701:ℤ))))), (.branch 166 (.branch 134 (.leaf (1835267736671417:ℤ)) (.branch 150 (.leaf (2027804401982480:ℤ)) (.leaf (2219056298075639:ℤ)))) (.branch 189 (.leaf (2431845583760126:ℤ)) (.branch 200 (.leaf (2781421461089177:ℤ)) (.leaf (2969465281681373:ℤ))))), (.branch 166 (.branch 134 (.leaf (1841516051604469:ℤ)) (.branch 150 (.leaf (2037192911302797:ℤ)) (.leaf (2232154508517356:ℤ)))) (.branch 189 (.leaf (2449739707655933:ℤ)) (.branch 200 (.leaf (2808659654333002:ℤ)) (.leaf (3002453037939040:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 8 8) 8000 (endpointMeanRuns 8 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 8 8, EndpointRunConditions (endpointMeanCutoff 8 8) (endpointMeanBox 8 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 8 8 h) (endpointMeanCornerA 8 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 8, endpointJoint24Q (endpointMeanCornerK 8 8 h) (endpointMeanCornerA 8 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 8 8, endpointRunWeightQ (endpointMeanCutoff 8 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 8 8) = (452989593/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 8 8 h = (logRoundedQ ((endpointMeanCutoff 8 8:ℚ)/200)).2+(452989593/1000000000000000:ℚ)+((endpointMeanRuns 8 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 8 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 8 8) r*endpointJoint24Q (endpointMeanCornerK 8 8 h) (endpointMeanCornerA 8 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 8 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 8 8 h≤endpointMeanCorner 8 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 8 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint08_08

namespace EndpointAnalyticJoint08_09
private noncomputable def weights : IntegerLookupTree := (.branch 1730 (.branch 1439 (.branch 1281 (.leaf (134313417400000:ℤ)) (.leaf (2749602000000:ℤ))) (.branch 1543 (.leaf (1257767900000:ℤ)) (.leaf (1778517800000:ℤ)))) (.branch 2561 (.branch 1940 (.leaf (1281478900000:ℤ)) (.leaf (2133036600000:ℤ))) (.branch 3765 (.leaf (782671000000:ℤ)) (.leaf (100335600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 174 (.branch 150 (.branch 134 (.leaf (1839149246076992:ℤ)) (.leaf (2033519860496594:ℤ))) (.branch 166 (.leaf (2226878851729186:ℤ)) (.leaf (2442316834382404:ℤ)))) (.branch 189 (.branch 183 (.leaf (2559241752835894:ℤ)) (.leaf (2698800707465438:ℤ))) (.branch 200 (.leaf (2796863493551838:ℤ)) (.leaf (2987865090803701:ℤ))))), (.branch 174 (.branch 150 (.branch 134 (.leaf (1845147090679372:ℤ)) (.leaf (2042525236372281:ℤ))) (.branch 166 (.leaf (2239434366279148:ℤ)) (.leaf (2459458575684252:ℤ)))) (.branch 189 (.branch 183 (.leaf (2579141763246633:ℤ)) (.leaf (2722233733371401:ℤ))) (.branch 200 (.leaf (2822932481206445:ℤ)) (.leaf (3019422791126066:ℤ))))), (.branch 174 (.branch 150 (.branch 134 (.leaf (1841516051604469:ℤ)) (.leaf (2037192911302797:ℤ))) (.branch 166 (.leaf (2232154508517356:ℤ)) (.leaf (2449739707655933:ℤ)))) (.branch 189 (.branch 183 (.leaf (2567991013838738:ℤ)) (.leaf (2709282267379919:ℤ))) (.branch 200 (.leaf (2808659654333002:ℤ)) (.leaf (3002453037939040:ℤ))))), (.branch 174 (.branch 150 (.branch 134 (.leaf (1847785639422515:ℤ)) (.leaf (2046624888379260:ℤ))) (.branch 166 (.leaf (2245330032507597:ℤ)) (.leaf (2467765500960413:ℤ)))) (.branch 189 (.branch 183 (.leaf (2588940614328977:ℤ)) (.leaf (2733983563717926:ℤ))) (.branch 200 (.leaf (2836164588587330:ℤ)) (.leaf (3035807254808191:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 8 9) 8000 (endpointMeanRuns 8 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 8 9, EndpointRunConditions (endpointMeanCutoff 8 9) (endpointMeanBox 8 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 8 9 h) (endpointMeanCornerA 8 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 9, endpointJoint24Q (endpointMeanCornerK 8 9 h) (endpointMeanCornerA 8 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 8 9, endpointRunWeightQ (endpointMeanCutoff 8 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 8 9) = (225855963/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 8 9 h = (logRoundedQ ((endpointMeanCutoff 8 9:ℚ)/200)).2+(225855963/500000000000000:ℚ)+((endpointMeanRuns 8 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 8 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 8 9) r*endpointJoint24Q (endpointMeanCornerK 8 9 h) (endpointMeanCornerA 8 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 8 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 8 9 h≤endpointMeanCorner 8 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 8 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint08_09

namespace EndpointAnalyticJoint08_10
private noncomputable def weights : IntegerLookupTree := (.branch 1940 (.branch 1281 (.leaf (131366538900000:ℤ)) (.branch 1439 (.leaf (2738041000000:ℤ)) (.leaf (6084396500000:ℤ)))) (.branch 2561 (.leaf (2125681100000:ℤ)) (.branch 3765 (.leaf (780240500000:ℤ)) (.leaf (100060100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 134 (.leaf (1845147090679372:ℤ)) (.branch 150 (.leaf (2042525236372281:ℤ)) (.leaf (2239434366279148:ℤ)))) (.branch 189 (.leaf (2459458575684252:ℤ)) (.branch 200 (.leaf (2822932481206445:ℤ)) (.leaf (3019422791126066:ℤ))))), (.branch 166 (.branch 134 (.leaf (1851164495488706:ℤ)) (.branch 150 (.leaf (2051570492259096:ℤ)) (.leaf (2252060670915195:ℤ)))) (.branch 189 (.leaf (2476720628687977:ℤ)) (.branch 200 (.leaf (2849244452517169:ℤ)) (.leaf (3051313802498079:ℤ))))), (.branch 166 (.branch 134 (.leaf (1847785639422515:ℤ)) (.branch 150 (.leaf (2046624888379260:ℤ)) (.leaf (2245330032507597:ℤ)))) (.branch 189 (.leaf (2467765500960413:ℤ)) (.branch 200 (.leaf (2836164588587330:ℤ)) (.leaf (3035807254808191:ℤ))))), (.branch 166 (.branch 134 (.leaf (1854076572550788:ℤ)) (.branch 150 (.leaf (2056100534462756:ℤ)) (.leaf (2258583326397622:ℤ)))) (.branch 189 (.leaf (2485923932529783:ℤ)) (.branch 200 (.leaf (2863938876021274:ℤ)) (.leaf (3069532003295625:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 8 10) 8000 (endpointMeanRuns 8 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 8 10, EndpointRunConditions (endpointMeanCutoff 8 10) (endpointMeanBox 8 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 8 10 h) (endpointMeanCornerA 8 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 10, endpointJoint24Q (endpointMeanCornerK 8 10 h) (endpointMeanCornerA 8 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 8 10, endpointRunWeightQ (endpointMeanCutoff 8 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 8 10) = (90139981/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 8 10 h = (logRoundedQ ((endpointMeanCutoff 8 10:ℚ)/200)).2+(90139981/200000000000000:ℚ)+((endpointMeanRuns 8 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 8 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 8 10) r*endpointJoint24Q (endpointMeanCornerK 8 10 h) (endpointMeanCornerA 8 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 8 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 8 10 h≤endpointMeanCorner 8 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 8 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint08_10

namespace EndpointAnalyticJoint08_11
private noncomputable def weights : IntegerLookupTree := (.branch 1730 (.branch 1281 (.leaf (127775991900000:ℤ)) (.branch 1439 (.leaf (2723731300000:ℤ)) (.leaf (3504582900000:ℤ)))) (.branch 2561 (.branch 1940 (.leaf (1270928900000:ℤ)) (.leaf (2116576700000:ℤ))) (.branch 3765 (.leaf (777232000000:ℤ)) (.leaf (99719100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 134 (.leaf (1851164495488706:ℤ)) (.branch 150 (.leaf (2051570492259096:ℤ)) (.leaf (2252060670915195:ℤ)))) (.branch 189 (.branch 174 (.leaf (2476720628687977:ℤ)) (.leaf (2599196511057195:ℤ))) (.branch 200 (.leaf (2849244452517169:ℤ)) (.leaf (3051313802498079:ℤ))))), (.branch 166 (.branch 134 (.leaf (1857201524294864:ℤ)) (.branch 150 (.leaf (2060655804764355:ℤ)) (.leaf (2264758164763642:ℤ)))) (.branch 189 (.branch 174 (.leaf (2494103837818031:ℤ)) (.leaf (2619407199466090:ℤ))) (.branch 200 (.leaf (2875801672284549:ℤ)) (.leaf (3083541645336467:ℤ))))), (.branch 166 (.branch 134 (.leaf (1854076572550788:ℤ)) (.branch 150 (.leaf (2056100534462756:ℤ)) (.leaf (2258583326397622:ℤ)))) (.branch 189 (.branch 174 (.leaf (2485923932529783:ℤ)) (.leaf (2610061121087325:ℤ))) (.branch 200 (.leaf (2863938876021274:ℤ)) (.leaf (3069532003295625:ℤ))))), (.branch 166 (.branch 134 (.leaf (1860388923661093:ℤ)) (.branch 150 (.leaf (2065620051735942:ℤ)) (.leaf (2271914849232334:ℤ)))) (.branch 189 (.branch 174 (.leaf (2504215978349345:ℤ)) (.leaf (2631353928362437:ℤ))) (.branch 200 (.leaf (2891985154384647:ℤ)) (.leaf (3103631399632896:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 8 11) 8000 (endpointMeanRuns 8 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 8 11, EndpointRunConditions (endpointMeanCutoff 8 11) (endpointMeanBox 8 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 8 11 h) (endpointMeanCornerA 8 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 11, endpointJoint24Q (endpointMeanCornerK 8 11 h) (endpointMeanCornerA 8 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 8 11, endpointRunWeightQ (endpointMeanCutoff 8 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 8 11) = (14045227/31250000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 8 11 h = (logRoundedQ ((endpointMeanCutoff 8 11:ℚ)/200)).2+(14045227/31250000000000:ℚ)+((endpointMeanRuns 8 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 8 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 8 11) r*endpointJoint24Q (endpointMeanCornerK 8 11 h) (endpointMeanCornerA 8 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 8 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 8 11 h≤endpointMeanCorner 8 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 8 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint08_11

namespace EndpointAnalyticJoint08_12
private noncomputable def weights : IntegerLookupTree := (.branch 1730 (.branch 1281 (.leaf (124285930900000:ℤ)) (.branch 1439 (.leaf (2709575700000:ℤ)) (.leaf (3487524000000:ℤ)))) (.branch 2561 (.branch 1940 (.leaf (1265156200000:ℤ)) (.leaf (2107570300000:ℤ))) (.branch 3765 (.leaf (774255900000:ℤ)) (.leaf (99381800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 134 (.leaf (1857201524294864:ℤ)) (.branch 150 (.leaf (2060655804764355:ℤ)) (.leaf (2264758164763642:ℤ)))) (.branch 189 (.branch 174 (.leaf (2494103837818031:ℤ)) (.leaf (2619407199466090:ℤ))) (.branch 200 (.leaf (2875801672284549:ℤ)) (.leaf (3083541645336467:ℤ))))), (.branch 166 (.branch 134 (.leaf (1863258241095736:ℤ)) (.branch 150 (.leaf (2069781351277481:ℤ)) (.leaf (2277527249201155:ℤ)))) (.branch 189 (.branch 174 (.leaf (2511609053425589:ℤ)) (.leaf (2639775041027588:ℤ))) (.branch 200 (.leaf (2902606426418855:ℤ)) (.leaf (3116109877240431:ℤ))))), (.branch 166 (.branch 134 (.leaf (1860388923661093:ℤ)) (.branch 150 (.leaf (2065620051735942:ℤ)) (.leaf (2271914849232334:ℤ)))) (.branch 189 (.branch 174 (.leaf (2504215978349345:ℤ)) (.leaf (2631353928362437:ℤ))) (.branch 200 (.leaf (2891985154384647:ℤ)) (.leaf (3103631399632896:ℤ))))), (.branch 166 (.branch 134 (.leaf (1866722765672653:ℤ)) (.branch 150 (.leaf (2075183643317552:ℤ)) (.leaf (2285325062766222:ℤ)))) (.branch 189 (.branch 174 (.leaf (2522642621585937:ℤ)) (.leaf (2652820441777222:ℤ))) (.branch 200 (.leaf (2920306087258494:ℤ)) (.leaf (3138109605778736:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 8 12) 8000 (endpointMeanRuns 8 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 8 12, EndpointRunConditions (endpointMeanCutoff 8 12) (endpointMeanBox 8 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 8 12 h) (endpointMeanCornerA 8 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 12, endpointJoint24Q (endpointMeanCornerK 8 12 h) (endpointMeanCornerA 8 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 8 12, endpointRunWeightQ (endpointMeanCutoff 8 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 8 12) = (224104053/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 8 12 h = (logRoundedQ ((endpointMeanCutoff 8 12:ℚ)/200)).2+(224104053/500000000000000:ℚ)+((endpointMeanRuns 8 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 8 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 8 12) r*endpointJoint24Q (endpointMeanCornerK 8 12 h) (endpointMeanCornerA 8 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 8 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 8 12 h≤endpointMeanCorner 8 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 8 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint08_12

namespace EndpointAnalyticJoint08_13
private noncomputable def weights : IntegerLookupTree := (.branch 1730 (.branch 1281 (.leaf (120893344100000:ℤ)) (.branch 1439 (.leaf (2695570800000:ℤ)) (.leaf (3470646700000:ℤ)))) (.branch 2561 (.branch 1940 (.leaf (1259445000000:ℤ)) (.leaf (2098659800000:ℤ))) (.branch 3765 (.leaf (771311500000:ℤ)) (.leaf (99048100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 134 (.leaf (1863258241095736:ℤ)) (.branch 150 (.leaf (2069781351277481:ℤ)) (.leaf (2277527249201155:ℤ)))) (.branch 189 (.branch 174 (.leaf (2511609053425589:ℤ)) (.leaf (2639775041027588:ℤ))) (.branch 200 (.leaf (2902606426418855:ℤ)) (.leaf (3116109877240431:ℤ))))), (.branch 166 (.branch 134 (.leaf (1869334710097930:ℤ)) (.branch 150 (.leaf (2078947309973447:ℤ)) (.leaf (2290368327867408:ℤ)))) (.branch 189 (.branch 174 (.leaf (2529237131830119:ℤ)) (.leaf (2660301257724491:ℤ))) (.branch 200 (.leaf (2929661022136860:ℤ)) (.leaf (3149022093384386:ℤ))))), (.branch 166 (.branch 134 (.leaf (1866722765672653:ℤ)) (.branch 150 (.leaf (2075183643317552:ℤ)) (.leaf (2285325062766222:ℤ)))) (.branch 189 (.branch 174 (.leaf (2522642621585937:ℤ)) (.leaf (2652820441777222:ℤ))) (.branch 200 (.leaf (2920306087258494:ℤ)) (.leaf (3138109605778736:ℤ))))), (.branch 166 (.branch 134 (.leaf (1873078171752951:ℤ)) (.branch 150 (.leaf (2084791513266747:ℤ)) (.leaf (2298814431479315:ℤ)))) (.branch 189 (.branch 174 (.leaf (2541204852640804:ℤ)) (.leaf (2674462078421619:ℤ))) (.branch 200 (.leaf (2948904364308072:ℤ)) (.leaf (3172970829927031:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 8 13) 8000 (endpointMeanRuns 8 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 8 13, EndpointRunConditions (endpointMeanCutoff 8 13) (endpointMeanBox 8 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 8 13 h) (endpointMeanCornerA 8 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 13, endpointJoint24Q (endpointMeanCornerK 8 13 h) (endpointMeanCornerA 8 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 8 13, endpointRunWeightQ (endpointMeanCutoff 8 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 8 13) = (223491073/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 8 13 h = (logRoundedQ ((endpointMeanCutoff 8 13:ℚ)/200)).2+(223491073/500000000000000:ℚ)+((endpointMeanRuns 8 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 8 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 8 13) r*endpointJoint24Q (endpointMeanCornerK 8 13 h) (endpointMeanCornerA 8 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 8 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 8 13 h≤endpointMeanCorner 8 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 8 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint08_13

namespace EndpointAnalyticJoint08_14
private noncomputable def weights : IntegerLookupTree := (.branch 1730 (.branch 1281 (.leaf (117595320800000:ℤ)) (.branch 1439 (.leaf (2681713400000:ℤ)) (.leaf (3453947300000:ℤ)))) (.branch 2561 (.branch 1940 (.leaf (1253794000000:ℤ)) (.leaf (2089843300000:ℤ))) (.branch 3765 (.leaf (768398200000:ℤ)) (.leaf (98717800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 166 (.branch 134 (.leaf (1869334710097930:ℤ)) (.branch 150 (.leaf (2078947309973447:ℤ)) (.leaf (2290368327867408:ℤ)))) (.branch 189 (.branch 174 (.leaf (2529237131830119:ℤ)) (.leaf (2660301257724491:ℤ))) (.branch 200 (.leaf (2929661022136860:ℤ)) (.leaf (3149022093384386:ℤ))))), (.branch 166 (.branch 134 (.leaf (1875430995717446:ℤ)) (.branch 150 (.leaf (2088153859816285:ℤ)) (.leaf (2303281806677886:ℤ)))) (.branch 189 (.branch 174 (.leaf (2546988935361303:ℤ)) (.leaf (2680987081041399:ℤ))) (.branch 200 (.leaf (2956967788160424:ℤ)) (.leaf (3182281926914820:ℤ))))), (.branch 166 (.branch 134 (.leaf (1873078171752951:ℤ)) (.branch 150 (.leaf (2084791513266747:ℤ)) (.leaf (2298814431479315:ℤ)))) (.branch 189 (.branch 174 (.leaf (2541204852640804:ℤ)) (.leaf (2674462078421619:ℤ))) (.branch 200 (.leaf (2948904364308072:ℤ)) (.leaf (3172970829927031:ℤ))))), (.branch 166 (.branch 134 (.leaf (1879455215318573:ℤ)) (.branch 150 (.leaf (2094443866587459:ℤ)) (.leaf (2312383422593279:ℤ)))) (.branch 189 (.branch 174 (.leaf (2559903669202779:ℤ)) (.leaf (2696280266946147:ℤ))) (.branch 200 (.leaf (2977782701538243:ℤ)) (.leaf (3208219327020436:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 8 14) 8000 (endpointMeanRuns 8 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 8 14, EndpointRunConditions (endpointMeanCutoff 8 14) (endpointMeanBox 8 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 8 14 h) (endpointMeanCornerA 8 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 8 14, endpointJoint24Q (endpointMeanCornerK 8 14 h) (endpointMeanCornerA 8 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 8 14, endpointRunWeightQ (endpointMeanCutoff 8 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 8 14) = (27860569/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 8 14 h = (logRoundedQ ((endpointMeanCutoff 8 14:ℚ)/200)).2+(27860569/62500000000000:ℚ)+((endpointMeanRuns 8 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 8 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 8 14) r*endpointJoint24Q (endpointMeanCornerK 8 14 h) (endpointMeanCornerA 8 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 8 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 8 14 h≤endpointMeanCorner 8 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 8 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint08_14

namespace EndpointAnalyticJoint09_01
private noncomputable def weights : IntegerLookupTree := (.branch 1238 (.leaf (163268254100000:ℤ)) (.branch 2171 (.leaf (21739963000000:ℤ)) (.leaf (9471963000000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.leaf (1788466363370219:ℤ)) (.branch 200 (.leaf (2219708490744480:ℤ)) (.leaf (2776108854772580:ℤ)))), (.branch 157 (.leaf (1789031108213300:ℤ)) (.branch 200 (.leaf (2221072934112558:ℤ)) (.leaf (2779012014842198:ℤ)))), (.branch 157 (.leaf (1788954710135412:ℤ)) (.branch 200 (.leaf (2220992723651733:ℤ)) (.leaf (2779099639744863:ℤ)))), (.branch 157 (.leaf (1789543868458404:ℤ)) (.branch 200 (.leaf (2222421781699088:ℤ)) (.leaf (2782154669837721:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 9 1) 8000 (endpointMeanRuns 9 1) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 9 1, EndpointRunConditions (endpointMeanCutoff 9 1) (endpointMeanBox 9 1).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 1, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 9 1 h) (endpointMeanCornerA 9 1 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 1, endpointJoint24Q (endpointMeanCornerK 9 1 h) (endpointMeanCornerA 9 1 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 9 1, endpointRunWeightQ (endpointMeanCutoff 9 1) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 9 1) = (461244261/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 9 1 h = (logRoundedQ ((endpointMeanCutoff 9 1:ℚ)/200)).2+(461244261/1000000000000000:ℚ)+((endpointMeanRuns 9 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 9 1).map (fun r => endpointRunWeightQ (endpointMeanCutoff 9 1) r*endpointJoint24Q (endpointMeanCornerK 9 1 h) (endpointMeanCornerA 9 1 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 9 1).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 9 1 h≤endpointMeanCorner 9 1 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 9 1 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint09_01

namespace EndpointAnalyticJoint09_02
private noncomputable def weights : IntegerLookupTree := (.branch 1238 (.leaf (161447846900000:ℤ)) (.branch 2171 (.leaf (21693715500000:ℤ)) (.leaf (9455717500000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.leaf (1789031108213300:ℤ)) (.branch 200 (.leaf (2221072934112558:ℤ)) (.leaf (2779012014842198:ℤ)))), (.branch 157 (.leaf (1795011250250668:ℤ)) (.branch 200 (.leaf (2235546180285696:ℤ)) (.leaf (2809884027910772:ℤ)))), (.branch 157 (.leaf (1789543868458404:ℤ)) (.branch 200 (.leaf (2222421781699088:ℤ)) (.leaf (2782154669837721:ℤ)))), (.branch 157 (.leaf (1795783016894429:ℤ)) (.branch 200 (.leaf (2237582945122589:ℤ)) (.leaf (2814651725239153:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 9 2) 8000 (endpointMeanRuns 9 2) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 9 2, EndpointRunConditions (endpointMeanCutoff 9 2) (endpointMeanBox 9 2).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 2, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 9 2 h) (endpointMeanCornerA 9 2 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 2, endpointJoint24Q (endpointMeanCornerK 9 2 h) (endpointMeanCornerA 9 2 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 9 2, endpointRunWeightQ (endpointMeanCutoff 9 2) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 9 2) = (460693463/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 9 2 h = (logRoundedQ ((endpointMeanCutoff 9 2:ℚ)/200)).2+(460693463/1000000000000000:ℚ)+((endpointMeanRuns 9 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 9 2).map (fun r => endpointRunWeightQ (endpointMeanCutoff 9 2) r*endpointJoint24Q (endpointMeanCornerK 9 2 h) (endpointMeanCornerA 9 2 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 9 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 9 2 h≤endpointMeanCorner 9 2 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 9 2 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint09_02

namespace EndpointAnalyticJoint09_03
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1238 (.leaf (156988076600000:ℤ)) (.leaf (5217707200000:ℤ))) (.branch 2171 (.leaf (8713100800000:ℤ)) (.leaf (9415440700000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 184 (.branch 157 (.leaf (1795011250250668:ℤ)) (.leaf (2235546180285696:ℤ))) (.branch 200 (.leaf (2579399512465253:ℤ)) (.leaf (2809884027910772:ℤ)))), (.branch 184 (.branch 157 (.leaf (1801011381934177:ℤ)) (.leaf (2250113738919978:ℤ))) (.branch 200 (.leaf (2603201845236441:ℤ)) (.leaf (2841098997823651:ℤ)))), (.branch 184 (.branch 157 (.leaf (1795783016894429:ℤ)) (.leaf (2237582945122589:ℤ))) (.branch 200 (.leaf (2582915989711995:ℤ)) (.leaf (2814651725239153:ℤ)))), (.branch 184 (.branch 157 (.leaf (1802043917785864:ℤ)) (.leaf (2252847536652426:ℤ))) (.branch 200 (.leaf (2607934822472328:ℤ)) (.leaf (2847528363638327:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 9 3) 8000 (endpointMeanRuns 9 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 9 3, EndpointRunConditions (endpointMeanCutoff 9 3) (endpointMeanBox 9 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 9 3 h) (endpointMeanCornerA 9 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 3, endpointJoint24Q (endpointMeanCornerK 9 3 h) (endpointMeanCornerA 9 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 9 3, endpointRunWeightQ (endpointMeanCutoff 9 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 9 3) = (28707993/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 9 3 h = (logRoundedQ ((endpointMeanCutoff 9 3:ℚ)/200)).2+(28707993/62500000000000:ℚ)+((endpointMeanRuns 9 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 9 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 9 3) r*endpointJoint24Q (endpointMeanCornerK 9 3 h) (endpointMeanCornerA 9 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 9 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 9 3 h≤endpointMeanCorner 9 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 9 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint09_03

namespace EndpointAnalyticJoint09_04
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1238 (.leaf (152655414200000:ℤ)) (.leaf (5189190400000:ℤ))) (.branch 2171 (.leaf (8670029900000:ℤ)) (.leaf (9375636100000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 184 (.branch 157 (.leaf (1801011381934177:ℤ)) (.leaf (2250113738919978:ℤ))) (.branch 200 (.leaf (2603201845236441:ℤ)) (.leaf (2841098997823651:ℤ)))), (.branch 184 (.branch 157 (.leaf (1807031570082637:ℤ)) (.leaf (2264776224586603:ℤ))) (.branch 200 (.leaf (2627223822557684:ℤ)) (.leaf (2872660734484549:ℤ)))), (.branch 184 (.branch 157 (.leaf (1802043917785864:ℤ)) (.leaf (2252847536652426:ℤ))) (.branch 200 (.leaf (2607934822472328:ℤ)) (.leaf (2847528363638327:ℤ)))), (.branch 184 (.branch 157 (.leaf (1808326646971479:ℤ)) (.leaf (2268216261865925:ℤ))) (.branch 200 (.leaf (2633195994509340:ℤ)) (.leaf (2880789018767791:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 9 4) 8000 (endpointMeanRuns 9 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 9 4, EndpointRunConditions (endpointMeanCutoff 9 4) (endpointMeanBox 9 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 9 4 h) (endpointMeanCornerA 9 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 4, endpointJoint24Q (endpointMeanCornerK 9 4 h) (endpointMeanCornerA 9 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 9 4, endpointRunWeightQ (endpointMeanCutoff 9 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 9 4) = (228989161/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 9 4 h = (logRoundedQ ((endpointMeanCutoff 9 4:ℚ)/200)).2+(228989161/500000000000000:ℚ)+((endpointMeanRuns 9 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 9 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 9 4) r*endpointJoint24Q (endpointMeanCornerK 9 4 h) (endpointMeanCornerA 9 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 9 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 9 4 h≤endpointMeanCorner 9 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 9 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint09_04

namespace EndpointAnalyticJoint09_05
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1238 (.leaf (148445925100000:ℤ)) (.leaf (5161004000000:ℤ))) (.branch 2171 (.leaf (8627458000000:ℤ)) (.leaf (9336292800000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 184 (.branch 157 (.leaf (1807031570082637:ℤ)) (.leaf (2264776224586603:ℤ))) (.branch 200 (.leaf (2627223822557684:ℤ)) (.leaf (2872660734484549:ℤ)))), (.branch 184 (.branch 157 (.leaf (1813071881738203:ℤ)) (.leaf (2279534255861525:ℤ))) (.branch 200 (.leaf (2651467471277744:ℤ)) (.leaf (2904573090121350:ℤ)))), (.branch 184 (.branch 157 (.leaf (1808326646971479:ℤ)) (.leaf (2268216261865925:ℤ))) (.branch 200 (.leaf (2633195994509340:ℤ)) (.leaf (2880789018767791:ℤ)))), (.branch 184 (.branch 157 (.leaf (1814631280554446:ℤ)) (.leaf (2283689831153794:ℤ))) (.branch 200 (.leaf (2658701853187751:ℤ)) (.leaf (2914438176148460:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 9 5) 8000 (endpointMeanRuns 9 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 9 5, EndpointRunConditions (endpointMeanCutoff 9 5) (endpointMeanBox 9 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 9 5 h) (endpointMeanCornerA 9 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 5, endpointJoint24Q (endpointMeanCornerK 9 5 h) (endpointMeanCornerA 9 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 9 5, endpointRunWeightQ (endpointMeanCutoff 9 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 9 5) = (91328879/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 9 5 h = (logRoundedQ ((endpointMeanCutoff 9 5:ℚ)/200)).2+(91328879/200000000000000:ℚ)+((endpointMeanRuns 9 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 9 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 9 5) r*endpointJoint24Q (endpointMeanCornerK 9 5 h) (endpointMeanCornerA 9 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 9 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 9 5 h≤endpointMeanCorner 9 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 9 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint09_05

namespace EndpointAnalyticJoint09_06
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1238 (.leaf (144355814300000:ℤ)) (.leaf (5133140500000:ℤ))) (.branch 2171 (.leaf (8585373800000:ℤ)) (.branch 3750 (.leaf (2990172800000:ℤ)) (.leaf (117120400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.branch 133 (.leaf (1813071881738203:ℤ)) (.leaf (1998256504356252:ℤ))) (.branch 184 (.leaf (2279534255861525:ℤ)) (.branch 200 (.leaf (2651467471277744:ℤ)) (.leaf (2904573090121350:ℤ))))), (.branch 157 (.branch 133 (.leaf (1819132384167129:ℤ)) (.leaf (2007360940869030:ℤ))) (.branch 184 (.leaf (2294388455351542:ℤ)) (.branch 200 (.leaf (2675934836948837:ℤ)) (.leaf (2936839959756291:ℤ))))), (.branch 157 (.branch 133 (.leaf (1814631280554446:ℤ)) (.leaf (2000683840904347:ℤ))) (.branch 184 (.leaf (2283689831153794:ℤ)) (.branch 200 (.leaf (2658701853187751:ℤ)) (.leaf (2914438176148460:ℤ))))), (.branch 157 (.branch 133 (.leaf (1820957894903265:ℤ)) (.leaf (2010206024023432:ℤ))) (.branch 184 (.leaf (2299268959752975:ℤ)) (.branch 200 (.leaf (2684454768609480:ℤ)) (.leaf (2948480373694528:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 9 6) 8000 (endpointMeanRuns 9 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 9 6, EndpointRunConditions (endpointMeanCutoff 9 6) (endpointMeanBox 9 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 9 6 h) (endpointMeanCornerA 9 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 6, endpointJoint24Q (endpointMeanCornerK 9 6 h) (endpointMeanCornerA 9 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 9 6, endpointRunWeightQ (endpointMeanCutoff 9 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 9 6) = (455325749/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 9 6 h = (logRoundedQ ((endpointMeanCutoff 9 6:ℚ)/200)).2+(455325749/1000000000000000:ℚ)+((endpointMeanRuns 9 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 9 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 9 6) r*endpointJoint24Q (endpointMeanCornerK 9 6 h) (endpointMeanCornerA 9 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 9 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 9 6 h≤endpointMeanCorner 9 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 9 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint09_06

namespace EndpointAnalyticJoint09_07
private noncomputable def weights : IntegerLookupTree := (.branch 1474 (.branch 1238 (.leaf (140381420100000:ℤ)) (.leaf (5105592600000:ℤ))) (.branch 2171 (.leaf (8543766200000:ℤ)) (.branch 3750 (.leaf (2977716300000:ℤ)) (.leaf (116709800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.branch 133 (.leaf (1819132384167129:ℤ)) (.leaf (2007360940869030:ℤ))) (.branch 184 (.leaf (2294388455351542:ℤ)) (.branch 200 (.leaf (2675934836948837:ℤ)) (.leaf (2936839959756291:ℤ))))), (.branch 157 (.branch 133 (.leaf (1825213144860533:ℤ)) (.leaf (2016506858925357:ℤ))) (.branch 184 (.leaf (2309339449720569:ℤ)) (.branch 200 (.leaf (2700627983999248:ℤ)) (.leaf (2969465281681373:ℤ))))), (.branch 157 (.branch 133 (.leaf (1820957894903265:ℤ)) (.leaf (2010206024023432:ℤ))) (.branch 184 (.leaf (2299268959752975:ℤ)) (.branch 200 (.leaf (2684454768609480:ℤ)) (.leaf (2948480373694528:ℤ))))), (.branch 157 (.branch 133 (.leaf (1827306566652699:ℤ)) (.leaf (2019773527632195:ℤ))) (.branch 184 (.leaf (2314954367779688:ℤ)) (.branch 200 (.leaf (2710457133833906:ℤ)) (.leaf (2982920202325470:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 9 7) 8000 (endpointMeanRuns 9 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 9 7, EndpointRunConditions (endpointMeanCutoff 9 7) (endpointMeanBox 9 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 9 7 h) (endpointMeanCornerA 9 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 7, endpointJoint24Q (endpointMeanCornerK 9 7 h) (endpointMeanCornerA 9 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 9 7, endpointRunWeightQ (endpointMeanCutoff 9 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 9 7) = (113505509/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 9 7 h = (logRoundedQ ((endpointMeanCutoff 9 7:ℚ)/200)).2+(113505509/250000000000000:ℚ)+((endpointMeanRuns 9 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 9 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 9 7) r*endpointJoint24Q (endpointMeanCornerK 9 7 h) (endpointMeanCornerA 9 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 9 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 9 7 h≤endpointMeanCorner 9 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 9 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint09_07

namespace EndpointAnalyticJoint09_08
private noncomputable def weights : IntegerLookupTree := (.branch 1719 (.branch 1238 (.leaf (136519208600000:ℤ)) (.branch 1474 (.leaf (5078353100000:ℤ)) (.leaf (3029572200000:ℤ)))) (.branch 2171 (.leaf (3030611100000:ℤ)) (.branch 3750 (.leaf (2965399300000:ℤ)) (.leaf (116303700000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 172 (.branch 133 (.leaf (1825213144860533:ℤ)) (.branch 157 (.leaf (2016506858925357:ℤ)) (.leaf (2309339449720569:ℤ)))) (.branch 184 (.leaf (2517775390491307:ℤ)) (.branch 200 (.leaf (2700627983999248:ℤ)) (.leaf (2969465281681373:ℤ))))), (.branch 172 (.branch 133 (.leaf (1831314231535121:ℤ)) (.branch 157 (.leaf (2025694447523037:ℤ)) (.leaf (2324387869716060:ℤ)))) (.branch 184 (.leaf (2537800335933370:ℤ)) (.branch 200 (.leaf (2725548995907509:ℤ)) (.leaf (3002453037939040:ℤ))))), (.branch 172 (.branch 133 (.leaf (1827306566652699:ℤ)) (.branch 157 (.leaf (2019773527632195:ℤ)) (.leaf (2314954367779688:ℤ)))) (.branch 184 (.leaf (2525479764683637:ℤ)) (.branch 200 (.leaf (2710457133833906:ℤ)) (.leaf (2982920202325470:ℤ))))), (.branch 172 (.branch 133 (.leaf (1833677372704686:ℤ)) (.branch 157 (.leaf (2029386567431877:ℤ)) (.leaf (2330746780262717:ℤ)))) (.branch 184 (.leaf (2546538361944001:ℤ)) (.branch 200 (.leaf (2736711365100251:ℤ)) (.leaf (3017762306585142:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 9 8) 8000 (endpointMeanRuns 9 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 9 8, EndpointRunConditions (endpointMeanCutoff 9 8) (endpointMeanBox 9 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 9 8 h) (endpointMeanCornerA 9 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 8, endpointJoint24Q (endpointMeanCornerK 9 8 h) (endpointMeanCornerA 9 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 9 8, endpointRunWeightQ (endpointMeanCutoff 9 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 9 8) = (226366461/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 9 8 h = (logRoundedQ ((endpointMeanCutoff 9 8:ℚ)/200)).2+(226366461/500000000000000:ℚ)+((endpointMeanRuns 9 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 9 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 9 8) r*endpointJoint24Q (endpointMeanCornerK 9 8 h) (endpointMeanCornerA 9 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 9 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 9 8 h≤endpointMeanCorner 9 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 9 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint09_08

namespace EndpointAnalyticJoint09_09
private noncomputable def weights : IntegerLookupTree := (.branch 1719 (.branch 1331 (.branch 1238 (.leaf (132765768600000:ℤ)) (.leaf (1951663300000:ℤ))) (.branch 1474 (.leaf (2448157900000:ℤ)) (.leaf (3014685100000:ℤ)))) (.branch 2526 (.branch 2171 (.leaf (3016800800000:ℤ)) (.leaf (797980100000:ℤ))) (.branch 3750 (.leaf (940418400000:ℤ)) (.leaf (115902200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 172 (.branch 149 (.branch 133 (.leaf (1831314231535121:ℤ)) (.leaf (2025694447523037:ℤ))) (.branch 157 (.leaf (2219337061989476:ℤ)) (.leaf (2324387869716060:ℤ)))) (.branch 193 (.branch 184 (.leaf (2537800335933370:ℤ)) (.leaf (2725548995907509:ℤ))) (.branch 200 (.leaf (2877342613417993:ℤ)) (.leaf (3002453037939040:ℤ))))), (.branch 172 (.branch 149 (.branch 133 (.leaf (1837435712133954:ℤ)) (.leaf (2034923896520976:ℤ))) (.branch 157 (.leaf (2232248734287348:ℤ)) (.leaf (2339534350195643:ℤ)))) (.branch 193 (.branch 184 (.leaf (2557984548338434:ℤ)) (.leaf (2750699975378214:ℤ))) (.branch 200 (.leaf (2906863390687500:ℤ)) (.leaf (3035807254808191:ℤ))))), (.branch 172 (.branch 149 (.branch 133 (.leaf (1833677372704686:ℤ)) (.leaf (2029386567431877:ℤ))) (.branch 157 (.leaf (2224670609798543:ℤ)) (.leaf (2330746780262717:ℤ)))) (.branch 193 (.branch 184 (.leaf (2546538361944001:ℤ)) (.leaf (2736711365100251:ℤ))) (.branch 200 (.leaf (2890693604110278:ℤ)) (.leaf (3017762306585142:ℤ))))), (.branch 172 (.branch 149 (.branch 133 (.leaf (1840070390229282:ℤ)) (.leaf (2039045360150354:ℤ))) (.branch 157 (.leaf (2238210171044355:ℤ)) (.leaf (2346646927176931:ℤ)))) (.branch 193 (.branch 184 (.leaf (2567772555352383:ℤ)) (.leaf (2763219902052073:ℤ))) (.branch 200 (.leaf (2921853880132133:ℤ)) (.leaf (3053011385268163:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 9 9) 8000 (endpointMeanRuns 9 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 9 9, EndpointRunConditions (endpointMeanCutoff 9 9) (endpointMeanBox 9 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 9 9 h) (endpointMeanCornerA 9 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 9, endpointJoint24Q (endpointMeanCornerK 9 9 h) (endpointMeanCornerA 9 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 9 9, endpointRunWeightQ (endpointMeanCutoff 9 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 9 9) = (90291617/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 9 9 h = (logRoundedQ ((endpointMeanCutoff 9 9:ℚ)/200)).2+(90291617/200000000000000:ℚ)+((endpointMeanRuns 9 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 9 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 9 9) r*endpointJoint24Q (endpointMeanCornerK 9 9 h) (endpointMeanCornerA 9 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 9 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 9 9 h≤endpointMeanCorner 9 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 9 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint09_09

namespace EndpointAnalyticJoint09_10
private noncomputable def weights : IntegerLookupTree := (.branch 1719 (.branch 1238 (.leaf (129117806000000:ℤ)) (.branch 1474 (.leaf (5024772600000:ℤ)) (.leaf (2999961000000:ℤ)))) (.branch 2526 (.branch 2171 (.leaf (3003141800000:ℤ)) (.leaf (794651500000:ℤ))) (.branch 3750 (.leaf (936761900000:ℤ)) (.leaf (115505100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.branch 133 (.leaf (1837435712133954:ℤ)) (.branch 149 (.leaf (2034923896520976:ℤ)) (.leaf (2232248734287348:ℤ)))) (.branch 184 (.branch 172 (.leaf (2339534350195643:ℤ)) (.leaf (2557984548338434:ℤ))) (.branch 200 (.leaf (2750699975378214:ℤ)) (.leaf (3035807254808191:ℤ))))), (.branch 157 (.branch 133 (.leaf (1843577654827210:ℤ)) (.branch 149 (.leaf (2044195396643119:ℤ)) (.leaf (2245235524188751:ℤ)))) (.branch 184 (.branch 172 (.leaf (2354779530153870:ℤ)) (.leaf (2578329294424829:ℤ))) (.branch 200 (.leaf (2776083044519398:ℤ)) (.leaf (3069532003295625:ℤ))))), (.branch 157 (.branch 133 (.leaf (1840070390229282:ℤ)) (.branch 149 (.leaf (2039045360150354:ℤ)) (.leaf (2238210171044355:ℤ)))) (.branch 184 (.branch 172 (.leaf (2346646927176931:ℤ)) (.leaf (2567772555352383:ℤ))) (.branch 200 (.leaf (2763219902052073:ℤ)) (.leaf (3053011385268163:ℤ))))), (.branch 157 (.branch 133 (.leaf (1846485696665587:ℤ)) (.branch 149 (.leaf (2048750123547003:ℤ)) (.leaf (2251832135373987:ℤ)))) (.branch 184 (.branch 172 (.leaf (2362655543477023:ℤ)) (.leaf (2589183809109213:ℤ))) (.branch 200 (.leaf (2789985207964000:ℤ)) (.leaf (3088672192053592:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 9 10) 8000 (endpointMeanRuns 9 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 9 10, EndpointRunConditions (endpointMeanCutoff 9 10) (endpointMeanBox 9 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 9 10 h) (endpointMeanCornerA 9 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 10, endpointJoint24Q (endpointMeanCornerK 9 10 h) (endpointMeanCornerA 9 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 9 10, endpointRunWeightQ (endpointMeanCutoff 9 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 9 10) = (112549303/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 9 10 h = (logRoundedQ ((endpointMeanCutoff 9 10:ℚ)/200)).2+(112549303/250000000000000:ℚ)+((endpointMeanRuns 9 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 9 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 9 10) r*endpointJoint24Q (endpointMeanCornerK 9 10 h) (endpointMeanCornerA 9 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 9 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 9 10 h≤endpointMeanCorner 9 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 9 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint09_10

namespace EndpointAnalyticJoint09_11
private noncomputable def weights : IntegerLookupTree := (.branch 1719 (.branch 1331 (.branch 1238 (.leaf (125572139500000:ℤ)) (.leaf (1930782000000:ℤ))) (.branch 1474 (.leaf (2423012400000:ℤ)) (.leaf (2985396500000:ℤ)))) (.branch 2526 (.branch 2171 (.leaf (2989630800000:ℤ)) (.leaf (791358900000:ℤ))) (.branch 3750 (.leaf (933145100000:ℤ)) (.leaf (115112200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 172 (.branch 149 (.branch 133 (.leaf (1843577654827210:ℤ)) (.leaf (2044195396643119:ℤ))) (.branch 157 (.leaf (2245235524188751:ℤ)) (.leaf (2354779530153870:ℤ)))) (.branch 193 (.branch 184 (.leaf (2578329294424829:ℤ)) (.leaf (2776083044519398:ℤ))) (.branch 200 (.leaf (2936687043355483:ℤ)) (.leaf (3069532003295625:ℤ))))), (.branch 172 (.branch 149 (.branch 133 (.leaf (1849740128012931:ℤ)) (.leaf (2053509139482373:ℤ))) (.branch 157 (.leaf (2258297868713327:ℤ)) (.leaf (2370124052749207:ℤ)))) (.branch 193 (.branch 184 (.leaf (2598835850985640:ℤ)) (.leaf (2801700345021616:ℤ))) (.branch 200 (.leaf (2966816678843751:ℤ)) (.leaf (3103631399632896:ℤ))))), (.branch 172 (.branch 149 (.branch 133 (.leaf (1846485696665587:ℤ)) (.leaf (2048750123547003:ℤ))) (.branch 157 (.leaf (2251832135373987:ℤ)) (.leaf (2362655543477023:ℤ)))) (.branch 193 (.branch 184 (.leaf (2589183809109213:ℤ)) (.leaf (2789985207964000:ℤ))) (.branch 200 (.leaf (2953350048827078:ℤ)) (.leaf (3088672192053592:ℤ))))), (.branch 172 (.branch 149 (.branch 133 (.leaf (1852923369722698:ℤ)) (.leaf (2058501076417622:ℤ))) (.branch 157 (.leaf (2265537004300601:ℤ)) (.leaf (2378773369131481:ℤ)))) (.branch 193 (.branch 184 (.leaf (2610773599624094:ℤ)) (.leaf (2817009769970615:ℤ))) (.branch 200 (.leaf (2985185730955324:ℤ)) (.leaf (3124749536145995:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 9 11) 8000 (endpointMeanRuns 9 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 9 11, EndpointRunConditions (endpointMeanCutoff 9 11) (endpointMeanBox 9 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 9 11 h) (endpointMeanCornerA 9 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 11, endpointJoint24Q (endpointMeanCornerK 9 11 h) (endpointMeanCornerA 9 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 9 11, endpointRunWeightQ (endpointMeanCutoff 9 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 9 11) = (448949999/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 9 11 h = (logRoundedQ ((endpointMeanCutoff 9 11:ℚ)/200)).2+(448949999/1000000000000000:ℚ)+((endpointMeanRuns 9 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 9 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 9 11) r*endpointJoint24Q (endpointMeanCornerK 9 11 h) (endpointMeanCornerA 9 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 9 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 9 11 h≤endpointMeanCorner 9 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 9 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint09_11

namespace EndpointAnalyticJoint09_12
private noncomputable def weights : IntegerLookupTree := (.branch 1719 (.branch 1331 (.branch 1238 (.leaf (122125695500000:ℤ)) (.leaf (1920509500000:ℤ))) (.branch 1474 (.leaf (2410642200000:ℤ)) (.leaf (2970988000000:ℤ)))) (.branch 2171 (.branch 1904 (.leaf (1267993700000:ℤ)) (.leaf (1158893800000:ℤ))) (.branch 2526 (.leaf (788101600000:ℤ)) (.branch 3750 (.leaf (929567100000:ℤ)) (.leaf (114723600000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 149 (.branch 133 (.leaf (1849740128012931:ℤ)) (.leaf (2053509139482373:ℤ))) (.branch 157 (.leaf (2258297868713327:ℤ)) (.leaf (2370124052749207:ℤ)))) (.branch 184 (.branch 172 (.leaf (2488862291385645:ℤ)) (.leaf (2598835850985640:ℤ))) (.branch 193 (.leaf (2801700345021616:ℤ)) (.branch 200 (.leaf (2966816678843751:ℤ)) (.leaf (3103631399632896:ℤ)))))), (.branch 165 (.branch 149 (.branch 133 (.leaf (1855923200317800:ℤ)) (.leaf (2062865317504599:ℤ))) (.branch 157 (.leaf (2271436207423207:ℤ)) (.leaf (2385568565331153:ℤ)))) (.branch 184 (.branch 172 (.leaf (2506935697216256:ℤ)) (.leaf (2619505504968840:ℤ))) (.branch 193 (.leaf (2827554038338631:ℤ)) (.branch 200 (.leaf (2997255436455438:ℤ)) (.leaf (3138109605778736:ℤ)))))), (.branch 165 (.branch 149 (.branch 133 (.leaf (1852923369722698:ℤ)) (.leaf (2058501076417622:ℤ))) (.branch 157 (.leaf (2265537004300601:ℤ)) (.leaf (2378773369131481:ℤ)))) (.branch 184 (.branch 172 (.leaf (2499150998181061:ℤ)) (.leaf (2610773599624094:ℤ))) (.branch 193 (.leaf (2817009769970615:ℤ)) (.branch 200 (.leaf (2985185730955324:ℤ)) (.leaf (3124749536145995:ℤ)))))), (.branch 165 (.branch 149 (.branch 133 (.leaf (1859383487380636:ℤ)) (.leaf (2068298438599360:ℤ))) (.branch 157 (.leaf (2279325282389629:ℤ)) (.leaf (2395001149156798:ℤ)))) (.branch 184 (.branch 172 (.leaf (2518164667399200:ℤ)) (.leaf (2632543415617601:ℤ))) (.branch 193 (.leaf (2844296099297558:ℤ)) (.branch 200 (.leaf (3017364586307133:ℤ)) (.leaf (3161248282924029:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 9 12) 8000 (endpointMeanRuns 9 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 9 12, EndpointRunConditions (endpointMeanCutoff 9 12) (endpointMeanBox 9 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 9 12 h) (endpointMeanCornerA 9 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 12, endpointJoint24Q (endpointMeanCornerK 9 12 h) (endpointMeanCornerA 9 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 9 12, endpointRunWeightQ (endpointMeanCutoff 9 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 9 12) = (223858077/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 9 12 h = (logRoundedQ ((endpointMeanCutoff 9 12:ℚ)/200)).2+(223858077/500000000000000:ℚ)+((endpointMeanRuns 9 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 9 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 9 12) r*endpointJoint24Q (endpointMeanCornerK 9 12 h) (endpointMeanCornerA 9 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 9 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 9 12 h≤endpointMeanCorner 9 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 9 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint09_12

namespace EndpointAnalyticJoint09_13
private noncomputable def weights : IntegerLookupTree := (.branch 1719 (.branch 1331 (.branch 1238 (.leaf (118775504200000:ℤ)) (.leaf (1910345900000:ℤ))) (.branch 1474 (.leaf (2398403200000:ℤ)) (.leaf (2956732400000:ℤ)))) (.branch 2171 (.branch 1904 (.leaf (1262256900000:ℤ)) (.leaf (1153890700000:ℤ))) (.branch 2526 (.leaf (784878900000:ℤ)) (.branch 3750 (.leaf (926027000000:ℤ)) (.leaf (114339100000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 149 (.branch 133 (.leaf (1855923200317800:ℤ)) (.leaf (2062865317504599:ℤ))) (.branch 157 (.leaf (2271436207423207:ℤ)) (.leaf (2385568565331153:ℤ)))) (.branch 184 (.branch 172 (.leaf (2506935697216256:ℤ)) (.leaf (2619505504968840:ℤ))) (.branch 193 (.leaf (2827554038338631:ℤ)) (.branch 200 (.leaf (2997255436455438:ℤ)) (.leaf (3138109605778736:ℤ)))))), (.branch 165 (.branch 149 (.branch 133 (.leaf (1862126940597888:ℤ)) (.leaf (2072264124052550:ℤ))) (.branch 157 (.leaf (2284650982437818:ℤ)) (.leaf (2401113719467543:ℤ)))) (.branch 184 (.branch 172 (.leaf (2525140346948725:ℤ)) (.leaf (2640339553558039:ℤ))) (.branch 193 (.leaf (2853646305869813:ℤ)) (.branch 200 (.leaf (3028006487702102:ℤ)) (.leaf (3172970829927031:ℤ)))))), (.branch 165 (.branch 149 (.branch 133 (.leaf (1859383487380636:ℤ)) (.leaf (2068298438599360:ℤ))) (.branch 157 (.leaf (2279325282389629:ℤ)) (.leaf (2395001149156798:ℤ)))) (.branch 184 (.branch 172 (.leaf (2518164667399200:ℤ)) (.leaf (2632543415617601:ℤ))) (.branch 193 (.leaf (2844296099297558:ℤ)) (.branch 200 (.leaf (3017364586307133:ℤ)) (.leaf (3161248282924029:ℤ)))))), (.branch 165 (.branch 149 (.branch 133 (.leaf (1865866127891288:ℤ)) (.leaf (2078142430975667:ℤ))) (.branch 157 (.leaf (2293197477277320:ℤ)) (.leaf (2411339633651886:ℤ)))) (.branch 184 (.branch 172 (.leaf (2537322993589799:ℤ)) (.leaf (2654494758223926:ℤ))) (.branch 193 (.leaf (2871846731494899:ℤ)) (.branch 200 (.leaf (3049890314123538:ℤ)) (.leaf (3198173354596575:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 9 13) 8000 (endpointMeanRuns 9 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 9 13, EndpointRunConditions (endpointMeanCutoff 9 13) (endpointMeanBox 9 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 9 13 h) (endpointMeanCornerA 9 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 13, endpointJoint24Q (endpointMeanCornerK 9 13 h) (endpointMeanCornerA 9 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 9 13, endpointRunWeightQ (endpointMeanCutoff 9 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 9 13) = (223247697/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 9 13 h = (logRoundedQ ((endpointMeanCutoff 9 13:ℚ)/200)).2+(223247697/500000000000000:ℚ)+((endpointMeanRuns 9 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 9 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 9 13) r*endpointJoint24Q (endpointMeanCornerK 9 13 h) (endpointMeanCornerA 9 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 9 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 9 13 h≤endpointMeanCorner 9 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 9 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint09_13

namespace EndpointAnalyticJoint09_14
private noncomputable def weights : IntegerLookupTree := (.branch 1719 (.branch 1331 (.branch 1238 (.leaf (115518695300000:ℤ)) (.leaf (1900289000000:ℤ))) (.branch 1474 (.leaf (2386292600000:ℤ)) (.leaf (2942626300000:ℤ)))) (.branch 2526 (.branch 2171 (.leaf (2949954400000:ℤ)) (.leaf (781690000000:ℤ))) (.branch 3750 (.leaf (922524000000:ℤ)) (.leaf (113958600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 172 (.branch 149 (.branch 133 (.leaf (1862126940597888:ℤ)) (.leaf (2072264124052550:ℤ))) (.branch 157 (.leaf (2284650982437818:ℤ)) (.leaf (2401113719467543:ℤ)))) (.branch 193 (.branch 184 (.leaf (2640339553558039:ℤ)) (.leaf (2853646305869813:ℤ))) (.branch 200 (.leaf (3028006487702102:ℤ)) (.leaf (3172970829927031:ℤ))))), (.branch 172 (.branch 149 (.branch 133 (.leaf (1868351417939431:ℤ)) (.leaf (2081705753349894:ℤ))) (.branch 157 (.leaf (2297942638448732:ℤ)) (.leaf (2416760170972045:ℤ)))) (.branch 193 (.branch 184 (.leaf (2661339304253910:ℤ)) (.leaf (2879979349144161:ℤ))) (.branch 200 (.leaf (3059073036634167:ℤ)) (.leaf (3208219327020436:ℤ))))), (.branch 172 (.branch 149 (.branch 133 (.leaf (1865866127891288:ℤ)) (.leaf (2078142430975667:ℤ))) (.branch 157 (.leaf (2293197477277320:ℤ)) (.leaf (2411339633651886:ℤ)))) (.branch 193 (.branch 184 (.leaf (2654494758223926:ℤ)) (.leaf (2871846731494899:ℤ))) (.branch 200 (.leaf (3049890314123538:ℤ)) (.leaf (3198173354596575:ℤ))))), (.branch 172 (.branch 149 (.branch 133 (.leaf (1872371369779375:ℤ)) (.leaf (2088033275481288:ℤ))) (.branch 157 (.leaf (2307154099689460:ℤ)) (.leaf (2427789577832786:ℤ)))) (.branch 193 (.branch 184 (.leaf (2676629141094418:ℤ)) (.leaf (2899664226672732:ℤ))) (.branch 200 (.leaf (3082766653521579:ℤ)) (.leaf (3235529730866545:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 9 14) 8000 (endpointMeanRuns 9 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 9 14, EndpointRunConditions (endpointMeanCutoff 9 14) (endpointMeanBox 9 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 9 14 h) (endpointMeanCornerA 9 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 14, endpointJoint24Q (endpointMeanCornerK 9 14 h) (endpointMeanCornerA 9 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 9 14, endpointRunWeightQ (endpointMeanCutoff 9 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 9 14) = (111321861/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 9 14 h = (logRoundedQ ((endpointMeanCutoff 9 14:ℚ)/200)).2+(111321861/250000000000000:ℚ)+((endpointMeanRuns 9 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 9 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 9 14) r*endpointJoint24Q (endpointMeanCornerK 9 14 h) (endpointMeanCornerA 9 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 9 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 9 14 h≤endpointMeanCorner 9 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 9 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint09_14

namespace EndpointAnalyticJoint09_15
private noncomputable def weights : IntegerLookupTree := (.branch 1719 (.branch 1238 (.leaf (112978615700000:ℤ)) (.branch 1474 (.leaf (4900799000000:ℤ)) (.leaf (2931447100000:ℤ)))) (.branch 2526 (.branch 2171 (.leaf (2939583800000:ℤ)) (.leaf (779162700000:ℤ))) (.branch 3750 (.leaf (919747900000:ℤ)) (.leaf (113657100000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 157 (.branch 133 (.leaf (1868351417939431:ℤ)) (.branch 149 (.leaf (2081705753349894:ℤ)) (.leaf (2297942638448732:ℤ)))) (.branch 184 (.branch 172 (.leaf (2416760170972045:ℤ)) (.leaf (2661339304253910:ℤ))) (.branch 200 (.leaf (2879979349144161:ℤ)) (.leaf (3208219327020436:ℤ))))), (.branch 157 (.branch 133 (.leaf (1874596701659598:ℤ)) (.branch 149 (.leaf (2091190400505222:ℤ)) (.leaf (2311311622734680:ℤ)))) (.branch 184 (.branch 172 (.leaf (2432508579931832:ℤ)) (.leaf (2682506074956243:ℤ))) (.branch 200 (.leaf (2906555390006065:ℤ)) (.leaf (3243859399269724:ℤ))))), (.branch 157 (.branch 133 (.leaf (1872371369779375:ℤ)) (.branch 149 (.leaf (2088033275481288:ℤ)) (.leaf (2307154099689460:ℤ)))) (.branch 184 (.branch 172 (.leaf (2427789577832786:ℤ)) (.leaf (2676629141094418:ℤ))) (.branch 200 (.leaf (2899664226672732:ℤ)) (.leaf (3235529730866545:ℤ))))), (.branch 157 (.branch 133 (.leaf (1878899291843383:ℤ)) (.branch 149 (.leaf (2097971195107255:ℤ)) (.leaf (2321195663460153:ℤ)))) (.branch 184 (.branch 172 (.leaf (2444351742067543:ℤ)) (.leaf (2698948090501926:ℤ))) (.branch 200 (.leaf (2927751169739095:ℤ)) (.leaf (3273322449602439:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 9 15) 8000 (endpointMeanRuns 9 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 9 15, EndpointRunConditions (endpointMeanCutoff 9 15) (endpointMeanBox 9 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 9 15 h) (endpointMeanCornerA 9 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 9 15, endpointJoint24Q (endpointMeanCornerK 9 15 h) (endpointMeanCornerA 9 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 9 15, endpointRunWeightQ (endpointMeanCutoff 9 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 9 15) = (27770633/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 9 15 h = (logRoundedQ ((endpointMeanCutoff 9 15:ℚ)/200)).2+(27770633/62500000000000:ℚ)+((endpointMeanRuns 9 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 9 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 9 15) r*endpointJoint24Q (endpointMeanCornerK 9 15 h) (endpointMeanCornerA 9 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 9 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 9 15 h≤endpointMeanCorner 9 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 9 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint09_15

namespace EndpointAnalyticJoint10_02
private noncomputable def weights : IntegerLookupTree := (.branch 1198 (.leaf (159604441600000:ℤ)) (.branch 2139 (.leaf (25979765300000:ℤ)) (.leaf (10975484900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 156 (.leaf (1781056077054601:ℤ)) (.branch 200 (.leaf (2212543367972096:ℤ)) (.leaf (2785690682236834:ℤ)))), (.branch 156 (.leaf (1786483621199157:ℤ)) (.branch 200 (.leaf (2225794790110707:ℤ)) (.leaf (2814651725239153:ℤ)))), (.branch 156 (.leaf (1781596134910617:ℤ)) (.branch 200 (.leaf (2213985971400352:ℤ)) (.leaf (2789168110391208:ℤ)))), (.branch 156 (.leaf (1787254093432159:ℤ)) (.branch 200 (.leaf (2227859064941132:ℤ)) (.leaf (2819650134446602:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 10 2) 8000 (endpointMeanRuns 10 2) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 10 2, EndpointRunConditions (endpointMeanCutoff 10 2) (endpointMeanBox 10 2).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 2, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 10 2 h) (endpointMeanCornerA 10 2 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 2, endpointJoint24Q (endpointMeanCornerK 10 2 h) (endpointMeanCornerA 10 2 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 10 2, endpointRunWeightQ (endpointMeanCutoff 10 2) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 10 2) = (460419049/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 10 2 h = (logRoundedQ ((endpointMeanCutoff 10 2:ℚ)/200)).2+(460419049/1000000000000000:ℚ)+((endpointMeanRuns 10 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 10 2).map (fun r => endpointRunWeightQ (endpointMeanCutoff 10 2) r*endpointJoint24Q (endpointMeanCornerK 10 2 h) (endpointMeanCornerA 10 2 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 10 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 10 2 h≤endpointMeanCorner 10 2 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 10 2 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint10_02

namespace EndpointAnalyticJoint10_03
private noncomputable def weights : IntegerLookupTree := (.branch 1711 (.branch 1198 (.leaf (155175812400000:ℤ)) (.leaf (13942285000000:ℤ))) (.branch 2139 (.leaf (3273913100000:ℤ)) (.leaf (10928604900000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 170 (.branch 156 (.leaf (1786483621199157:ℤ)) (.leaf (2225794790110707:ℤ))) (.branch 200 (.leaf (2397144980767770:ℤ)) (.leaf (2814651725239153:ℤ)))), (.branch 170 (.branch 156 (.leaf (1792597419587484:ℤ)) (.leaf (2240768187289274:ℤ))) (.branch 200 (.leaf (2416623336972081:ℤ)) (.leaf (2847528363638327:ℤ)))), (.branch 170 (.branch 156 (.leaf (1787254093432159:ℤ)) (.leaf (2227859064941132:ℤ))) (.branch 200 (.leaf (2399913967557402:ℤ)) (.leaf (2819650134446602:ℤ)))), (.branch 170 (.branch 156 (.leaf (1793628305653154:ℤ)) (.leaf (2243539497699914:ℤ))) (.branch 200 (.leaf (2420346035478664:ℤ)) (.leaf (2854272749503711:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 10 3) 8000 (endpointMeanRuns 10 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 10 3, EndpointRunConditions (endpointMeanCutoff 10 3) (endpointMeanBox 10 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 10 3 h) (endpointMeanCornerA 10 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 3, endpointJoint24Q (endpointMeanCornerK 10 3 h) (endpointMeanCornerA 10 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 10 3, endpointRunWeightQ (endpointMeanCutoff 10 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 10 3) = (229528353/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 10 3 h = (logRoundedQ ((endpointMeanCutoff 10 3:ℚ)/200)).2+(229528353/500000000000000:ℚ)+((endpointMeanRuns 10 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 10 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 10 3) r*endpointJoint24Q (endpointMeanCornerK 10 3 h) (endpointMeanCornerA 10 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 10 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 10 3 h≤endpointMeanCorner 10 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 10 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint10_03

namespace EndpointAnalyticJoint10_04
private noncomputable def weights : IntegerLookupTree := (.branch 1711 (.branch 1198 (.leaf (150873429600000:ℤ)) (.leaf (13866919600000:ℤ))) (.branch 2139 (.leaf (3258461400000:ℤ)) (.leaf (10882273300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 170 (.branch 156 (.leaf (1792597419587484:ℤ)) (.leaf (2240768187289274:ℤ))) (.branch 200 (.leaf (2416623336972081:ℤ)) (.leaf (2847528363638327:ℤ)))), (.branch 170 (.branch 156 (.leaf (1798732140938829:ℤ)) (.leaf (2255842313710295:ℤ))) (.branch 200 (.leaf (2436259967441596:ℤ)) (.leaf (2880789018767791:ℤ)))), (.branch 170 (.branch 156 (.leaf (1793628305653154:ℤ)) (.leaf (2243539497699914:ℤ))) (.branch 200 (.leaf (2420346035478664:ℤ)) (.leaf (2854272749503711:ℤ)))), (.branch 170 (.branch 156 (.leaf (1800025251396814:ℤ)) (.leaf (2259330294698237:ℤ))) (.branch 200 (.leaf (2440952055218692:ℤ)) (.leaf (2889320497260344:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 10 4) 8000 (endpointMeanRuns 10 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 10 4, EndpointRunConditions (endpointMeanCutoff 10 4) (endpointMeanBox 10 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 10 4 h) (endpointMeanCornerA 10 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 4, endpointJoint24Q (endpointMeanCornerK 10 4 h) (endpointMeanCornerA 10 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 10 4, endpointRunWeightQ (endpointMeanCutoff 10 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 10 4) = (228855149/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 10 4 h = (logRoundedQ ((endpointMeanCutoff 10 4:ℚ)/200)).2+(228855149/500000000000000:ℚ)+((endpointMeanRuns 10 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 10 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 10 4) r*endpointJoint24Q (endpointMeanCornerK 10 4 h) (endpointMeanCornerA 10 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 10 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 10 4 h≤endpointMeanCorner 10 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 10 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint10_04

namespace EndpointAnalyticJoint10_05
private noncomputable def weights : IntegerLookupTree := (.branch 1711 (.branch 1198 (.leaf (146693388500000:ℤ)) (.leaf (13792425400000:ℤ))) (.branch 2139 (.leaf (3243188200000:ℤ)) (.branch 3742 (.leaf (3531680700000:ℤ)) (.leaf (133070000000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 156 (.branch 132 (.leaf (1798732140938829:ℤ)) (.leaf (1980519545954784:ℤ))) (.branch 170 (.leaf (2255842313710295:ℤ)) (.branch 200 (.leaf (2436259967441596:ℤ)) (.leaf (2880789018767791:ℤ))))), (.branch 156 (.branch 132 (.leaf (1804887856856851:ℤ)) (.leaf (1989793866464427:ℤ))) (.branch 170 (.leaf (2271017847000910:ℤ)) (.branch 200 (.leaf (2456056158257273:ℤ)) (.leaf (2914438176148460:ℤ))))), (.branch 156 (.branch 132 (.leaf (1800025251396814:ℤ)) (.leaf (1982543567941936:ℤ))) (.branch 170 (.leaf (2259330294698237:ℤ)) (.branch 200 (.leaf (2440952055218692:ℤ)) (.leaf (2889320497260344:ℤ))))), (.branch 156 (.branch 132 (.leaf (1806445011741869:ℤ)) (.leaf (1992234315800021:ℤ))) (.branch 170 (.leaf (2275232232717297:ℤ)) (.branch 200 (.leaf (2461733507745321:ℤ)) (.leaf (2924798597940690:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 10 5) 8000 (endpointMeanRuns 10 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 10 5, EndpointRunConditions (endpointMeanCutoff 10 5) (endpointMeanBox 10 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 10 5 h) (endpointMeanCornerA 10 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 5, endpointJoint24Q (endpointMeanCornerK 10 5 h) (endpointMeanCornerA 10 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 10 5, endpointRunWeightQ (endpointMeanCutoff 10 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 10 5) = (91275891/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 10 5 h = (logRoundedQ ((endpointMeanCutoff 10 5:ℚ)/200)).2+(91275891/200000000000000:ℚ)+((endpointMeanRuns 10 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 10 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 10 5) r*endpointJoint24Q (endpointMeanCornerK 10 5 h) (endpointMeanCornerA 10 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 10 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 10 5 h≤endpointMeanCorner 10 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 10 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint10_05

namespace EndpointAnalyticJoint10_06
private noncomputable def weights : IntegerLookupTree := (.branch 1711 (.branch 1198 (.leaf (142631922500000:ℤ)) (.leaf (13718782600000:ℤ))) (.branch 2139 (.leaf (3228089700000:ℤ)) (.branch 3742 (.leaf (3516816700000:ℤ)) (.leaf (132600300000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 156 (.branch 132 (.leaf (1804887856856851:ℤ)) (.leaf (1989793866464427:ℤ))) (.branch 170 (.leaf (2271017847000910:ℤ)) (.branch 200 (.leaf (2456056158257273:ℤ)) (.leaf (2914438176148460:ℤ))))), (.branch 156 (.branch 132 (.leaf (1811064639190268:ℤ)) (.leaf (1999111616497949:ℤ))) (.branch 170 (.leaf (2286295469346798:ℤ)) (.branch 200 (.leaf (2476013205950318:ℤ)) (.leaf (2948480373694528:ℤ))))), (.branch 156 (.branch 132 (.leaf (1806445011741869:ℤ)) (.leaf (1992234315800021:ℤ))) (.branch 170 (.leaf (2275232232717297:ℤ)) (.branch 200 (.leaf (2461733507745321:ℤ)) (.leaf (2924798597940690:ℤ))))), (.branch 156 (.branch 132 (.leaf (1812887668056220:ℤ)) (.leaf (2001972432399746:ℤ))) (.branch 170 (.leaf (2291246094005545:ℤ)) (.branch 200 (.leaf (2482691886634832:ℤ)) (.leaf (2960712335868302:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 10 6) 8000 (endpointMeanRuns 10 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 10 6, EndpointRunConditions (endpointMeanCutoff 10 6) (endpointMeanBox 10 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 10 6 h) (endpointMeanCornerA 10 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 6, endpointJoint24Q (endpointMeanCornerK 10 6 h) (endpointMeanCornerA 10 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 10 6, endpointRunWeightQ (endpointMeanCutoff 10 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 10 6) = (227531911/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 10 6 h = (logRoundedQ ((endpointMeanCutoff 10 6:ℚ)/200)).2+(227531911/500000000000000:ℚ)+((endpointMeanRuns 10 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 10 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 10 6) r*endpointJoint24Q (endpointMeanCornerK 10 6 h) (endpointMeanCornerA 10 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 10 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 10 6 h≤endpointMeanCorner 10 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 10 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint10_06

namespace EndpointAnalyticJoint10_07
private noncomputable def weights : IntegerLookupTree := (.branch 1711 (.branch 1198 (.leaf (138685397400000:ℤ)) (.branch 1377 (.leaf (4617559000000:ℤ)) (.leaf (5705000200000:ℤ)))) (.branch 2139 (.leaf (3213161700000:ℤ)) (.branch 3742 (.leaf (3502120600000:ℤ)) (.leaf (132136000000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 170 (.branch 132 (.leaf (1811064639190268:ℤ)) (.branch 156 (.leaf (1999111616497949:ℤ)) (.leaf (2286295469346798:ℤ)))) (.branch 187 (.leaf (2476013205950318:ℤ)) (.branch 200 (.leaf (2731765558877218:ℤ)) (.leaf (2948480373694528:ℤ))))), (.branch 170 (.branch 132 (.leaf (1817262560033678:ℤ)) (.branch 156 (.leaf (2008472999425890:ℤ)) (.leaf (2301675867522851:ℤ)))) (.branch 187 (.leaf (2496132417587080:ℤ)) (.branch 200 (.leaf (2759199811470909:ℤ)) (.leaf (2982920202325470:ℤ))))), (.branch 170 (.branch 132 (.leaf (1812887668056220:ℤ)) (.branch 156 (.leaf (2001972432399746:ℤ)) (.leaf (2291246094005545:ℤ)))) (.branch 187 (.leaf (2482691886634832:ℤ)) (.branch 200 (.leaf (2741225515706610:ℤ)) (.leaf (2960712335868302:ℤ))))), (.branch 170 (.branch 132 (.leaf (1819353301997962:ℤ)) (.branch 156 (.leaf (2011758149281301:ℤ)) (.leaf (2307372666317169:ℤ)))) (.branch 187 (.leaf (2503828698179339:ℤ)) (.branch 200 (.leaf (2770122464365757:ℤ)) (.leaf (2997067060253181:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 10 7) 8000 (endpointMeanRuns 10 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 10 7, EndpointRunConditions (endpointMeanCutoff 10 7) (endpointMeanBox 10 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 10 7 h) (endpointMeanCornerA 10 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 7, endpointJoint24Q (endpointMeanCornerK 10 7 h) (endpointMeanCornerA 10 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 10 7, endpointRunWeightQ (endpointMeanCutoff 10 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 10 7) = (28360191/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 10 7 h = (logRoundedQ ((endpointMeanCutoff 10 7:ℚ)/200)).2+(28360191/62500000000000:ℚ)+((endpointMeanRuns 10 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 10 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 10 7) r*endpointJoint24Q (endpointMeanCornerK 10 7 h) (endpointMeanCornerA 10 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 10 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 10 7 h≤endpointMeanCorner 10 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 10 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint10_07

namespace EndpointAnalyticJoint10_08
private noncomputable def weights : IntegerLookupTree := (.branch 1711 (.branch 1198 (.leaf (134850305600000:ℤ)) (.branch 1377 (.leaf (4592406100000:ℤ)) (.leaf (5676241300000:ℤ)))) (.branch 2139 (.leaf (3198400600000:ℤ)) (.branch 3742 (.leaf (3487588800000:ℤ)) (.leaf (131676800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 170 (.branch 132 (.leaf (1817262560033678:ℤ)) (.branch 156 (.leaf (2008472999425890:ℤ)) (.leaf (2301675867522851:ℤ)))) (.branch 187 (.leaf (2496132417587080:ℤ)) (.branch 200 (.leaf (2759199811470909:ℤ)) (.leaf (2982920202325470:ℤ))))), (.branch 170 (.branch 132 (.leaf (1823481691728400:ℤ)) (.branch 156 (.leaf (2017878219571122:ℤ)) (.leaf (2317159732924039:ℤ)))) (.branch 187 (.leaf (2516415110854684:ℤ)) (.branch 200 (.leaf (2786909577537168:ℤ)) (.leaf (3017762306585142:ℤ))))), (.branch 170 (.branch 132 (.leaf (1819353301997962:ℤ)) (.branch 156 (.leaf (2011758149281301:ℤ)) (.leaf (2307372666317169:ℤ)))) (.branch 187 (.leaf (2503828698179339:ℤ)) (.branch 200 (.leaf (2770122464365757:ℤ)) (.leaf (2997067060253181:ℤ))))), (.branch 170 (.branch 132 (.leaf (1825841995516429:ℤ)) (.branch 156 (.leaf (2021591699116664:ℤ)) (.leaf (2323612742950830:ℤ)))) (.branch 187 (.leaf (2525145461495017:ℤ)) (.branch 200 (.leaf (2799324033581303:ℤ)) (.leaf (3033868185988537:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 10 8) 8000 (endpointMeanRuns 10 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 10 8, EndpointRunConditions (endpointMeanCutoff 10 8) (endpointMeanBox 10 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 10 8 h) (endpointMeanCornerA 10 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 8, endpointJoint24Q (endpointMeanCornerK 10 8 h) (endpointMeanCornerA 10 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 10 8, endpointRunWeightQ (endpointMeanCutoff 10 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 10 8) = (452476823/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 10 8 h = (logRoundedQ ((endpointMeanCutoff 10 8:ℚ)/200)).2+(452476823/1000000000000000:ℚ)+((endpointMeanRuns 10 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 10 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 10 8) r*endpointJoint24Q (endpointMeanCornerK 10 8 h) (endpointMeanCornerA 10 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 10 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 10 8 h≤endpointMeanCorner 10 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 10 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint10_08

namespace EndpointAnalyticJoint10_09
private noncomputable def weights : IntegerLookupTree := (.branch 1711 (.branch 1377 (.branch 1198 (.leaf (131123260900000:ℤ)) (.leaf (4567531200000:ℤ))) (.branch 1556 (.leaf (3030059600000:ℤ)) (.leaf (1739196200000:ℤ)))) (.branch 2139 (.branch 1901 (.leaf (1475767600000:ℤ)) (.leaf (1163812500000:ℤ))) (.branch 2495 (.leaf (947178600000:ℤ)) (.branch 3742 (.leaf (1113912600000:ℤ)) (.leaf (131222700000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 148 (.branch 132 (.leaf (1823481691728400:ℤ)) (.leaf (2017878219571122:ℤ))) (.branch 156 (.leaf (2211822905243556:ℤ)) (.leaf (2317159732924039:ℤ)))) (.branch 177 (.branch 170 (.leaf (2414312961511738:ℤ)) (.leaf (2516415110854684:ℤ))) (.branch 187 (.leaf (2623771823434287:ℤ)) (.branch 200 (.leaf (2786909577537168:ℤ)) (.leaf (3017762306585142:ℤ)))))), (.branch 163 (.branch 148 (.branch 132 (.leaf (1829722106863329:ℤ)) (.leaf (2027327482213319:ℤ))) (.branch 156 (.leaf (2225088496136080:ℤ)) (.leaf (2332747761596498:ℤ)))) (.branch 177 (.branch 170 (.leaf (2432195083812639:ℤ)) (.leaf (2536862614147299:ℤ))) (.branch 187 (.leaf (2647084349021478:ℤ)) (.branch 200 (.leaf (2814897623970171:ℤ)) (.leaf (3053011385268163:ℤ)))))), (.branch 163 (.branch 148 (.branch 132 (.leaf (1825841995516429:ℤ)) (.leaf (2021591699116664:ℤ))) (.branch 156 (.leaf (2217219404313199:ℤ)) (.leaf (2323612742950830:ℤ)))) (.branch 177 (.branch 170 (.leaf (2421830515404249:ℤ)) (.leaf (2525145461495017:ℤ))) (.branch 187 (.leaf (2633882124964312:ℤ)) (.branch 200 (.leaf (2799324033581303:ℤ)) (.leaf (3033868185988537:ℤ)))))), (.branch 163 (.branch 148 (.branch 132 (.leaf (1832353830853211:ℤ)) (.leaf (2031473315715124:ℤ))) (.branch 156 (.leaf (2231121385417458:ℤ)) (.leaf (2339967122788701:ℤ)))) (.branch 177 (.branch 170 (.leaf (2440611242822691:ℤ)) (.leaf (2546643708631287:ℤ))) (.branch 187 (.leaf (2658420253318989:ℤ)) (.branch 200 (.leaf (2828833434546394:ℤ)) (.leaf (3071121194457298:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 10 9) 8000 (endpointMeanRuns 10 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 10 9, EndpointRunConditions (endpointMeanCutoff 10 9) (endpointMeanBox 10 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 10 9 h) (endpointMeanCornerA 10 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 9, endpointJoint24Q (endpointMeanCornerK 10 9 h) (endpointMeanCornerA 10 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 10 9, endpointRunWeightQ (endpointMeanCutoff 10 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 10 9) = (451204803/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 10 9 h = (logRoundedQ ((endpointMeanCutoff 10 9:ℚ)/200)).2+(451204803/1000000000000000:ℚ)+((endpointMeanRuns 10 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 10 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 10 9) r*endpointJoint24Q (endpointMeanCornerK 10 9 h) (endpointMeanCornerA 10 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 10 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 10 9 h≤endpointMeanCorner 10 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 10 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint10_09

namespace EndpointAnalyticJoint10_10
private noncomputable def weights : IntegerLookupTree := (.branch 1711 (.branch 1198 (.leaf (127500993400000:ℤ)) (.branch 1377 (.leaf (4542928100000:ℤ)) (.leaf (5619669900000:ℤ)))) (.branch 2495 (.branch 2139 (.leaf (3169364100000:ℤ)) (.leaf (943212100000:ℤ))) (.branch 3742 (.leaf (1109571900000:ℤ)) (.leaf (130773600000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 156 (.branch 132 (.leaf (1829722106863329:ℤ)) (.branch 148 (.leaf (2027327482213319:ℤ)) (.leaf (2225088496136080:ℤ)))) (.branch 187 (.branch 170 (.leaf (2332747761596498:ℤ)) (.leaf (2536862614147299:ℤ))) (.branch 200 (.leaf (2814897623970171:ℤ)) (.leaf (3053011385268163:ℤ))))), (.branch 156 (.branch 132 (.leaf (1835983878275775:ℤ)) (.branch 148 (.leaf (2036820993593431:ℤ)) (.leaf (2238433648507648:ℤ)))) (.branch 187 (.branch 170 (.leaf (2348440654268812:ℤ)) (.leaf (2557476266653177:ℤ))) (.branch 200 (.leaf (2843166745451117:ℤ)) (.leaf (3088672192053592:ℤ))))), (.branch 156 (.branch 132 (.leaf (1832353830853211:ℤ)) (.branch 148 (.leaf (2031473315715124:ℤ)) (.leaf (2231121385417458:ℤ)))) (.branch 187 (.branch 170 (.leaf (2339967122788701:ℤ)) (.leaf (2546643708631287:ℤ))) (.branch 200 (.leaf (2828833434546394:ℤ)) (.leaf (3071121194457298:ℤ))))), (.branch 156 (.branch 132 (.leaf (1838888890543234:ℤ)) (.branch 148 (.leaf (2041403234028828:ℤ)) (.leaf (2245110532040043:ℤ)))) (.branch 187 (.branch 170 (.leaf (2356436610335760:ℤ)) (.leaf (2568324984680934:ℤ))) (.branch 200 (.leaf (2858653912305333:ℤ)) (.leaf (3108831634348551:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 10 10) 8000 (endpointMeanRuns 10 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 10 10, EndpointRunConditions (endpointMeanCutoff 10 10) (endpointMeanBox 10 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 10 10 h) (endpointMeanCornerA 10 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 10, endpointJoint24Q (endpointMeanCornerK 10 10 h) (endpointMeanCornerA 10 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 10 10, endpointRunWeightQ (endpointMeanCutoff 10 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 10 10) = (224973343/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 10 10 h = (logRoundedQ ((endpointMeanCutoff 10 10:ℚ)/200)).2+(224973343/500000000000000:ℚ)+((endpointMeanRuns 10 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 10 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 10 10) r*endpointJoint24Q (endpointMeanCornerK 10 10 h) (endpointMeanCornerA 10 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 10 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 10 10 h≤endpointMeanCorner 10 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 10 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint10_10

namespace EndpointAnalyticJoint10_11
private noncomputable def weights : IntegerLookupTree := (.branch 1711 (.branch 1377 (.branch 1198 (.leaf (123980344900000:ℤ)) (.leaf (4518591000000:ℤ))) (.branch 1556 (.leaf (2999577300000:ℤ)) (.leaf (1722554600000:ℤ)))) (.branch 2139 (.branch 1901 (.leaf (1462235100000:ℤ)) (.leaf (1153612400000:ℤ))) (.branch 2495 (.leaf (939288600000:ℤ)) (.branch 3742 (.leaf (1105278100000:ℤ)) (.leaf (130329300000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 148 (.branch 132 (.leaf (1835983878275775:ℤ)) (.leaf (2036820993593431:ℤ))) (.branch 156 (.leaf (2238433648507648:ℤ)) (.leaf (2348440654268812:ℤ)))) (.branch 177 (.branch 170 (.leaf (2450209653854610:ℤ)) (.leaf (2557476266653177:ℤ))) (.branch 187 (.leaf (2670604009178982:ℤ)) (.branch 200 (.leaf (2843166745451117:ℤ)) (.leaf (3088672192053592:ℤ)))))), (.branch 163 (.branch 148 (.branch 132 (.leaf (1842267079052318:ℤ)) (.leaf (2046358960918185:ℤ))) (.branch 156 (.leaf (2251858839534813:ℤ)) (.leaf (2364239116383510:ℤ)))) (.branch 177 (.branch 170 (.leaf (2468357652640007:ℤ)) (.leaf (2578257418442330:ℤ))) (.branch 187 (.leaf (2694332644322163:ℤ)) (.branch 200 (.leaf (2871719764727320:ℤ)) (.leaf (3124749536145995:ℤ)))))), (.branch 163 (.branch 148 (.branch 132 (.leaf (1838888890543234:ℤ)) (.leaf (2041403234028828:ℤ))) (.branch 156 (.leaf (2245110532040043:ℤ)) (.leaf (2356436610335760:ℤ)))) (.branch 177 (.branch 170 (.leaf (2459537610375782:ℤ)) (.leaf (2568324984680934:ℤ))) (.branch 187 (.leaf (2683186987098886:ℤ)) (.branch 200 (.leaf (2858653912305333:ℤ)) (.leaf (3108831634348551:ℤ)))))), (.branch 163 (.branch 148 (.branch 132 (.leaf (1845447257415761:ℤ)) (.leaf (2051381690158395:ℤ))) (.branch 156 (.leaf (2259187390709364:ℤ)) (.leaf (2373022015759366:ℤ)))) (.branch 177 (.branch 170 (.leaf (2478610747468602:ℤ)) (.leaf (2590190847891140:ℤ))) (.branch 187 (.leaf (2708184456068734:ℤ)) (.branch 200 (.leaf (2888788746110450:ℤ)) (.leaf (3147005122483997:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 10 11) 8000 (endpointMeanRuns 10 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 10 11, EndpointRunConditions (endpointMeanCutoff 10 11) (endpointMeanBox 10 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 10 11 h) (endpointMeanCornerA 10 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 11, endpointJoint24Q (endpointMeanCornerK 10 11 h) (endpointMeanCornerA 10 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 10 11, endpointRunWeightQ (endpointMeanCutoff 10 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 10 11) = (44870217/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 10 11 h = (logRoundedQ ((endpointMeanCutoff 10 11:ℚ)/200)).2+(44870217/100000000000000:ℚ)+((endpointMeanRuns 10 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 10 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 10 11) r*endpointJoint24Q (endpointMeanCornerK 10 11 h) (endpointMeanCornerA 10 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 10 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 10 11 h≤endpointMeanCorner 10 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 10 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint10_11

namespace EndpointAnalyticJoint10_12
private noncomputable def weights : IntegerLookupTree := (.branch 1711 (.branch 1261 (.branch 1198 (.leaf (120558264000000:ℤ)) (.leaf (1553039900000:ℤ))) (.branch 1377 (.leaf (2509524100000:ℤ)) (.branch 1556 (.leaf (2984581100000:ℤ)) (.leaf (1714367500000:ℤ))))) (.branch 2495 (.branch 1901 (.leaf (1455577600000:ℤ)) (.branch 2139 (.leaf (1148594200000:ℤ)) (.leaf (935407000000:ℤ)))) (.branch 2994 (.leaf (522490800000:ℤ)) (.branch 3742 (.leaf (208282400000:ℤ)) (.leaf (129889800000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 140 (.branch 132 (.leaf (1842267079052318:ℤ)) (.leaf (2046358960918185:ℤ))) (.branch 148 (.leaf (2146052201161361:ℤ)) (.branch 156 (.leaf (2251858839534813:ℤ)) (.leaf (2364239116383510:ℤ))))) (.branch 187 (.branch 170 (.leaf (2468357652640007:ℤ)) (.branch 177 (.leaf (2578257418442330:ℤ)) (.leaf (2694332644322163:ℤ)))) (.branch 195 (.leaf (2871719764727320:ℤ)) (.branch 200 (.leaf (3024250430665177:ℤ)) (.leaf (3124749536145995:ℤ)))))), (.branch 163 (.branch 140 (.branch 132 (.leaf (1848571782529653:ℤ)) (.leaf (2055941592364613:ℤ))) (.branch 148 (.leaf (2157461860485541:ℤ)) (.branch 156 (.leaf (2265364549256040:ℤ)) (.leaf (2380143858128797:ℤ))))) (.branch 187 (.branch 170 (.leaf (2486640068437188:ℤ)) (.branch 177 (.leaf (2599207430554962:ℤ)) (.leaf (2718272111218694:ℤ)))) (.branch 195 (.leaf (2900559532894029:ℤ)) (.branch 200 (.leaf (3057615024664566:ℤ)) (.leaf (3161248282924029:ℤ)))))), (.branch 163 (.branch 140 (.branch 132 (.leaf (1845447257415761:ℤ)) (.leaf (2051381690158395:ℤ))) (.branch 148 (.leaf (2152136662966362:ℤ)) (.branch 156 (.leaf (2259187390709364:ℤ)) (.leaf (2373022015759366:ℤ))))) (.branch 187 (.branch 170 (.leaf (2478610747468602:ℤ)) (.branch 177 (.leaf (2590190847891140:ℤ)) (.leaf (2708184456068734:ℤ)))) (.branch 195 (.leaf (2888788746110450:ℤ)) (.branch 200 (.leaf (3044361901790125:ℤ)) (.leaf (3147005122483997:ℤ)))))), (.branch 163 (.branch 140 (.branch 132 (.leaf (1852029014595478:ℤ)) (.leaf (2061408921358491:ℤ))) (.branch 148 (.leaf (2164089187151605:ℤ)) (.branch 156 (.leaf (2273352511380563:ℤ)) (.leaf (2389724154929110:ℤ))))) (.branch 187 (.branch 170 (.leaf (2497831792264485:ℤ)) (.branch 177 (.leaf (2612242869775494:ℤ)) (.leaf (2733414809834873:ℤ)))) (.branch 195 (.leaf (2919241249782687:ℤ)) (.branch 200 (.leaf (3079648909505721:ℤ)) (.leaf (3185647344654546:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 10 12) 8000 (endpointMeanRuns 10 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 10 12, EndpointRunConditions (endpointMeanCutoff 10 12) (endpointMeanBox 10 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 10 12 h) (endpointMeanCornerA 10 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 12, endpointJoint24Q (endpointMeanCornerK 10 12 h) (endpointMeanCornerA 10 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 10 12, endpointRunWeightQ (endpointMeanCutoff 10 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 10 12) = (111867741/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 10 12 h = (logRoundedQ ((endpointMeanCutoff 10 12:ℚ)/200)).2+(111867741/250000000000000:ℚ)+((endpointMeanRuns 10 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 10 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 10 12) r*endpointJoint24Q (endpointMeanCornerK 10 12 h) (endpointMeanCornerA 10 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 10 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 10 12 h≤endpointMeanCorner 10 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 10 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint10_12

namespace EndpointAnalyticJoint10_13
private noncomputable def weights : IntegerLookupTree := (.branch 1711 (.branch 1261 (.branch 1198 (.leaf (116577731800000:ℤ)) (.leaf (1542985600000:ℤ))) (.branch 1377 (.leaf (2493818300000:ℤ)) (.branch 1556 (.leaf (2966794900000:ℤ)) (.leaf (1704657200000:ℤ))))) (.branch 2495 (.branch 1901 (.leaf (1447681400000:ℤ)) (.branch 2139 (.leaf (1142642500000:ℤ)) (.leaf (930803200000:ℤ)))) (.branch 2994 (.leaf (520069700000:ℤ)) (.branch 3742 (.leaf (207379000000:ℤ)) (.leaf (129368500000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 140 (.branch 132 (.leaf (1848571782529653:ℤ)) (.leaf (2055941592364613:ℤ))) (.branch 148 (.leaf (2157461860485541:ℤ)) (.branch 156 (.leaf (2265364549256040:ℤ)) (.leaf (2380143858128797:ℤ))))) (.branch 187 (.branch 170 (.leaf (2486640068437188:ℤ)) (.branch 177 (.leaf (2599207430554962:ℤ)) (.leaf (2718272111218694:ℤ)))) (.branch 195 (.leaf (2900559532894029:ℤ)) (.branch 200 (.leaf (3057615024664566:ℤ)) (.leaf (3161248282924029:ℤ)))))), (.branch 163 (.branch 140 (.branch 132 (.leaf (1854898062295460:ℤ)) (.leaf (2065569097084597:ℤ))) (.branch 148 (.leaf (2168932180182207:ℤ)) (.branch 156 (.leaf (2278951260588860:ℤ)) (.leaf (2396155594470455:ℤ))))) (.branch 187 (.branch 170 (.leaf (2505057896834329:ℤ)) (.branch 177 (.leaf (2620327675090619:ℤ)) (.leaf (2742424283133854:ℤ)))) (.branch 195 (.leaf (2929688929679146:ℤ)) (.branch 200 (.leaf (3091347708595081:ℤ)) (.leaf (3198173354596575:ℤ)))))), (.branch 163 (.branch 140 (.branch 132 (.leaf (1852029014595478:ℤ)) (.leaf (2061408921358491:ℤ))) (.branch 148 (.leaf (2164089187151605:ℤ)) (.branch 156 (.leaf (2273352511380563:ℤ)) (.leaf (2389724154929110:ℤ))))) (.branch 187 (.branch 170 (.leaf (2497831792264485:ℤ)) (.branch 177 (.leaf (2612242869775494:ℤ)) (.leaf (2733414809834873:ℤ)))) (.branch 195 (.leaf (2919241249782687:ℤ)) (.branch 200 (.leaf (3079648909505721:ℤ)) (.leaf (3185647344654546:ℤ)))))), (.branch 163 (.branch 140 (.branch 132 (.leaf (1858634245503523:ℤ)) (.leaf (2071485166043515:ℤ))) (.branch 148 (.leaf (2176108093196724:ℤ)) (.branch 156 (.leaf (2287606447457006:ℤ)) (.leaf (2406543849456959:ℤ))))) (.branch 187 (.branch 170 (.leaf (2517201891752972:ℤ)) (.branch 177 (.leaf (2634482635226925:ℤ)) (.leaf (2758880218030091:ℤ)))) (.branch 195 (.leaf (2950014772076018:ℤ)) (.branch 200 (.leaf (3115344926712855:ℤ)) (.leaf (3224764056467202:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 10 13) 8000 (endpointMeanRuns 10 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 10 13, EndpointRunConditions (endpointMeanCutoff 10 13) (endpointMeanBox 10 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 10 13 h) (endpointMeanCornerA 10 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 13, endpointJoint24Q (endpointMeanCornerK 10 13 h) (endpointMeanCornerA 10 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 10 13, endpointRunWeightQ (endpointMeanCutoff 10 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 10 13) = (111502673/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 10 13 h = (logRoundedQ ((endpointMeanCutoff 10 13:ℚ)/200)).2+(111502673/250000000000000:ℚ)+((endpointMeanRuns 10 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 10 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 10 13) r*endpointJoint24Q (endpointMeanCornerK 10 13 h) (endpointMeanCornerA 10 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 10 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 10 13 h≤endpointMeanCorner 10 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 10 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint10_13

namespace EndpointAnalyticJoint10_14
private noncomputable def weights : IntegerLookupTree := (.branch 1711 (.branch 1261 (.branch 1198 (.leaf (113362259800000:ℤ)) (.leaf (1534703400000:ℤ))) (.branch 1377 (.leaf (2480880500000:ℤ)) (.branch 1556 (.leaf (2952143500000:ℤ)) (.leaf (1696658400000:ℤ))))) (.branch 2495 (.branch 1901 (.leaf (1441177000000:ℤ)) (.branch 2139 (.leaf (1137739700000:ℤ)) (.leaf (927010800000:ℤ)))) (.branch 2994 (.leaf (518075300000:ℤ)) (.branch 3742 (.leaf (206634900000:ℤ)) (.leaf (128939000000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 140 (.branch 132 (.leaf (1854898062295460:ℤ)) (.leaf (2065569097084597:ℤ))) (.branch 148 (.leaf (2168932180182207:ℤ)) (.branch 156 (.leaf (2278951260588860:ℤ)) (.leaf (2396155594470455:ℤ))))) (.branch 187 (.branch 170 (.leaf (2505057896834329:ℤ)) (.branch 177 (.leaf (2620327675090619:ℤ)) (.leaf (2742424283133854:ℤ)))) (.branch 195 (.leaf (2929688929679146:ℤ)) (.branch 200 (.leaf (3091347708595081:ℤ)) (.leaf (3198173354596575:ℤ)))))), (.branch 163 (.branch 140 (.branch 132 (.leaf (1861245992189249:ℤ)) (.leaf (2075241685209417:ℤ))) (.branch 148 (.leaf (2180463482757111:ℤ)) (.branch 156 (.leaf (2292619459347132:ℤ)) (.leaf (2412275045183997:ℤ))))) (.branch 187 (.branch 170 (.leaf (2523612140793645:ℤ)) (.branch 177 (.leaf (2641619535298038:ℤ)) (.leaf (2766791049977093:ℤ)))) (.branch 195 (.leaf (2959110863730755:ℤ)) (.branch 200 (.leaf (3125452543354259:ℤ)) (.leaf (3235529730866545:ℤ)))))), (.branch 163 (.branch 140 (.branch 132 (.leaf (1858634245503523:ℤ)) (.leaf (2071485166043515:ℤ))) (.branch 148 (.leaf (2176108093196724:ℤ)) (.branch 156 (.leaf (2287606447457006:ℤ)) (.leaf (2406543849456959:ℤ))))) (.branch 187 (.branch 170 (.leaf (2517201891752972:ℤ)) (.branch 177 (.leaf (2634482635226925:ℤ)) (.leaf (2758880218030091:ℤ)))) (.branch 195 (.leaf (2950014772076018:ℤ)) (.branch 200 (.leaf (3115344926712855:ℤ)) (.leaf (3224764056467202:ℤ)))))), (.branch 163 (.branch 140 (.branch 132 (.leaf (1865263033858567:ℤ)) (.leaf (2081610663793224:ℤ))) (.branch 148 (.leaf (2188193749772915:ℤ)) (.branch 156 (.leaf (2301949755811905:ℤ)) (.leaf (2423481926737652:ℤ))))) (.branch 187 (.branch 170 (.leaf (2536722201818229:ℤ)) (.branch 177 (.leaf (2656911742631611:ℤ)) (.leaf (2784582870500207:ℤ)))) (.branch 195 (.leaf (2981112697045694:ℤ)) (.branch 200 (.leaf (3151454694214877:ℤ)) (.leaf (3264361084202336:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 10 14) 8000 (endpointMeanRuns 10 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 10 14, EndpointRunConditions (endpointMeanCutoff 10 14) (endpointMeanBox 10 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 10 14 h) (endpointMeanCornerA 10 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 14, endpointJoint24Q (endpointMeanCornerK 10 14 h) (endpointMeanCornerA 10 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 10 14, endpointRunWeightQ (endpointMeanCutoff 10 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 10 14) = (444807791/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 10 14 h = (logRoundedQ ((endpointMeanCutoff 10 14:ℚ)/200)).2+(444807791/1000000000000000:ℚ)+((endpointMeanRuns 10 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 10 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 10 14) r*endpointJoint24Q (endpointMeanCornerK 10 14 h) (endpointMeanCornerA 10 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 10 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 10 14 h≤endpointMeanCorner 10 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 10 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint10_14

namespace EndpointAnalyticJoint10_15
private noncomputable def weights : IntegerLookupTree := (.branch 1711 (.branch 1377 (.branch 1198 (.leaf (110236262100000:ℤ)) (.leaf (4419154500000:ℤ))) (.branch 1556 (.leaf (2937643500000:ℤ)) (.leaf (1688742200000:ℤ)))) (.branch 2139 (.branch 1901 (.leaf (1434739800000:ℤ)) (.leaf (1132887700000:ℤ))) (.branch 2495 (.leaf (923257700000:ℤ)) (.branch 3742 (.leaf (1087734500000:ℤ)) (.leaf (128514000000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 163 (.branch 148 (.branch 132 (.leaf (1861245992189249:ℤ)) (.leaf (2075241685209417:ℤ))) (.branch 156 (.leaf (2292619459347132:ℤ)) (.leaf (2412275045183997:ℤ)))) (.branch 177 (.branch 170 (.leaf (2523612140793645:ℤ)) (.leaf (2641619535298038:ℤ))) (.branch 187 (.leaf (2766791049977093:ℤ)) (.branch 200 (.leaf (2959110863730755:ℤ)) (.leaf (3235529730866545:ℤ)))))), (.branch 163 (.branch 148 (.branch 132 (.leaf (1867615646303228:ℤ)) (.leaf (2084959567854360:ℤ))) (.branch 156 (.leaf (2306369634258443:ℤ)) (.leaf (2428502934887025:ℤ)))) (.branch 177 (.branch 170 (.leaf (2542303810706009:ℤ)) (.leaf (2663084405665751:ℤ))) (.branch 187 (.leaf (2791374318449947:ℤ)) (.branch 200 (.leaf (2988828272907585:ℤ)) (.leaf (3273322449602439:ℤ)))))), (.branch 163 (.branch 148 (.branch 132 (.leaf (1865263033858567:ℤ)) (.leaf (2081610663793224:ℤ))) (.branch 156 (.leaf (2301949755811905:ℤ)) (.leaf (2423481926737652:ℤ)))) (.branch 177 (.branch 170 (.leaf (2536722201818229:ℤ)) (.leaf (2656911742631611:ℤ))) (.branch 187 (.leaf (2784582870500207:ℤ)) (.branch 200 (.leaf (2981112697045694:ℤ)) (.leaf (3264361084202336:ℤ)))))), (.branch 163 (.branch 148 (.branch 132 (.leaf (1871915463677856:ℤ)) (.leaf (2091785655358460:ℤ))) (.branch 156 (.leaf (2316382996810065:ℤ)) (.leaf (2440539219989433:ℤ)))) (.branch 177 (.branch 170 (.leaf (2556393887308041:ℤ)) (.leaf (2679531803983852:ℤ))) (.branch 187 (.leaf (2810524977492367:ℤ)) (.branch 200 (.leaf (3012538444420391:ℤ)) (.leaf (3304444325681487:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 10 15) 8000 (endpointMeanRuns 10 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 10 15, EndpointRunConditions (endpointMeanCutoff 10 15) (endpointMeanBox 10 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 10 15 h) (endpointMeanCornerA 10 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 10 15, endpointJoint24Q (endpointMeanCornerK 10 15 h) (endpointMeanCornerA 10 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 10 15, endpointRunWeightQ (endpointMeanCutoff 10 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 10 15) = (443617329/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 10 15 h = (logRoundedQ ((endpointMeanCutoff 10 15:ℚ)/200)).2+(443617329/1000000000000000:ℚ)+((endpointMeanRuns 10 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 10 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 10 15) r*endpointJoint24Q (endpointMeanCornerK 10 15 h) (endpointMeanCornerA 10 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 10 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 10 15 h≤endpointMeanCorner 10 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 10 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint10_15

namespace EndpointAnalyticJoint11_02
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 1161 (.leaf (157671002600000:ℤ)) (.leaf (10432812900000:ℤ))) (.branch 2417 (.leaf (12827280400000:ℤ)) (.leaf (5158219600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 178 (.branch 148 (.leaf (1782979684152100:ℤ)) (.leaf (2126648768836515:ℤ))) (.branch 200 (.leaf (2488936420752411:ℤ)) (.leaf (2796600258601426:ℤ)))), (.branch 178 (.branch 148 (.leaf (1787254093432159:ℤ)) (.leaf (2135607814397781:ℤ))) (.branch 200 (.leaf (2504705775992466:ℤ)) (.leaf (2819650134446602:ℤ)))), (.branch 178 (.branch 148 (.leaf (1783591025059058:ℤ)) (.leaf (2128034478086529:ℤ))) (.branch 200 (.leaf (2491555968135071:ℤ)) (.leaf (2800641491261003:ℤ)))), (.branch 178 (.branch 148 (.leaf (1788044027818037:ℤ)) (.leaf (2137401659219153:ℤ))) (.branch 200 (.leaf (2508104229542936:ℤ)) (.leaf (2824903231995377:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 11 2) 8000 (endpointMeanRuns 11 2) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 11 2, EndpointRunConditions (endpointMeanCutoff 11 2) (endpointMeanBox 11 2).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 2, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 11 2 h) (endpointMeanCornerA 11 2 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 2, endpointJoint24Q (endpointMeanCornerK 11 2 h) (endpointMeanCornerA 11 2 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 11 2, endpointRunWeightQ (endpointMeanCutoff 11 2) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 11 2) = (460145287/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 11 2 h = (logRoundedQ ((endpointMeanCutoff 11 2:ℚ)/200)).2+(460145287/1000000000000000:ℚ)+((endpointMeanRuns 11 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 11 2).map (fun r => endpointRunWeightQ (endpointMeanCutoff 11 2) r*endpointJoint24Q (endpointMeanCornerK 11 2 h) (endpointMeanCornerA 11 2 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 11 2).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 11 2 h≤endpointMeanCorner 11 2 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 11 2 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint11_02

namespace EndpointAnalyticJoint11_03
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 1161 (.leaf (153273979100000:ℤ)) (.leaf (10374536600000:ℤ))) (.branch 2417 (.leaf (12764293200000:ℤ)) (.leaf (5137042400000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 178 (.branch 148 (.leaf (1787254093432159:ℤ)) (.leaf (2135607814397781:ℤ))) (.branch 200 (.leaf (2504705775992466:ℤ)) (.leaf (2819650134446602:ℤ)))), (.branch 178 (.branch 148 (.leaf (1793628305653154:ℤ)) (.leaf (2148998090264982:ℤ))) (.branch 200 (.leaf (2528336805059548:ℤ)) (.leaf (2854272749503711:ℤ)))), (.branch 178 (.branch 148 (.leaf (1788044027818037:ℤ)) (.leaf (2137401659219153:ℤ))) (.branch 200 (.leaf (2508104229542936:ℤ)) (.leaf (2824903231995377:ℤ)))), (.branch 178 (.branch 148 (.leaf (1794685385739962:ℤ)) (.leaf (2151405216794840:ℤ))) (.branch 200 (.leaf (2532911861480200:ℤ)) (.leaf (2861365084220703:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 11 3) 8000 (endpointMeanRuns 11 3) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 11 3, EndpointRunConditions (endpointMeanCutoff 11 3) (endpointMeanBox 11 3).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 3, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 11 3 h) (endpointMeanCornerA 11 3 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 3, endpointJoint24Q (endpointMeanCornerK 11 3 h) (endpointMeanCornerA 11 3 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 11 3, endpointRunWeightQ (endpointMeanCutoff 11 3) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 11 3) = (229393081/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 11 3 h = (logRoundedQ ((endpointMeanCutoff 11 3:ℚ)/200)).2+(229393081/500000000000000:ℚ)+((endpointMeanRuns 11 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 11 3).map (fun r => endpointRunWeightQ (endpointMeanCutoff 11 3) r*endpointJoint24Q (endpointMeanCornerK 11 3 h) (endpointMeanCornerA 11 3 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 11 3).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 11 3 h≤endpointMeanCorner 11 3 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 11 3 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint11_03

namespace EndpointAnalyticJoint11_04
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 1161 (.leaf (149002339200000:ℤ)) (.leaf (10316940300000:ℤ))) (.branch 2417 (.leaf (12702040900000:ℤ)) (.leaf (5116112300000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 178 (.branch 148 (.leaf (1793628305653154:ℤ)) (.leaf (2148998090264982:ℤ))) (.branch 200 (.leaf (2528336805059548:ℤ)) (.leaf (2854272749503711:ℤ)))), (.branch 178 (.branch 148 (.leaf (1800025251396814:ℤ)) (.leaf (2162472323255112:ℤ))) (.branch 200 (.leaf (2552190784678402:ℤ)) (.leaf (2889320497260344:ℤ)))), (.branch 178 (.branch 148 (.leaf (1794685385739962:ℤ)) (.leaf (2151405216794840:ℤ))) (.branch 200 (.leaf (2532911861480200:ℤ)) (.leaf (2861365084220703:ℤ)))), (.branch 178 (.branch 148 (.leaf (1801351411754144:ℤ)) (.leaf (2165500521106069:ℤ))) (.branch 200 (.leaf (2557964865437931:ℤ)) (.leaf (2898297560236838:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 11 4) 8000 (endpointMeanRuns 11 4) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 11 4, EndpointRunConditions (endpointMeanCutoff 11 4) (endpointMeanBox 11 4).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 4, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 11 4 h) (endpointMeanCornerA 11 4 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 4, endpointJoint24Q (endpointMeanCornerK 11 4 h) (endpointMeanCornerA 11 4 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 11 4, endpointRunWeightQ (endpointMeanCutoff 11 4) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 11 4) = (91488579/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 11 4 h = (logRoundedQ ((endpointMeanCutoff 11 4:ℚ)/200)).2+(91488579/200000000000000:ℚ)+((endpointMeanRuns 11 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 11 4).map (fun r => endpointRunWeightQ (endpointMeanCutoff 11 4) r*endpointJoint24Q (endpointMeanCornerK 11 4 h) (endpointMeanCornerA 11 4 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 11 4).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 11 4 h≤endpointMeanCorner 11 4 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 11 4 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint11_04

namespace EndpointAnalyticJoint11_05
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 1161 (.leaf (144852208000000:ℤ)) (.leaf (10260008400000:ℤ))) (.branch 2417 (.leaf (12640506700000:ℤ)) (.leaf (5095423600000:ℤ))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 178 (.branch 148 (.leaf (1800025251396814:ℤ)) (.leaf (2162472323255112:ℤ))) (.branch 200 (.leaf (2552190784678402:ℤ)) (.leaf (2889320497260344:ℤ)))), (.branch 178 (.branch 148 (.leaf (1806445011741869:ℤ)) (.leaf (2176031039779914:ℤ))) (.branch 200 (.leaf (2576269818310042:ℤ)) (.leaf (2924798597940690:ℤ)))), (.branch 178 (.branch 148 (.leaf (1801351411754144:ℤ)) (.leaf (2165500521106069:ℤ))) (.branch 200 (.leaf (2557964865437931:ℤ)) (.leaf (2898297560236838:ℤ)))), (.branch 178 (.branch 148 (.leaf (1808042197485646:ℤ)) (.leaf (2179688173247484:ℤ))) (.branch 200 (.leaf (2583265668388140:ℤ)) (.leaf (2935706734522691:ℤ))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 11 5) 8000 (endpointMeanRuns 11 5) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 11 5, EndpointRunConditions (endpointMeanCutoff 11 5) (endpointMeanBox 11 5).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 5, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 11 5 h) (endpointMeanCornerA 11 5 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 5, endpointJoint24Q (endpointMeanCornerK 11 5 h) (endpointMeanCornerA 11 5 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 11 5, endpointRunWeightQ (endpointMeanCutoff 11 5) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 11 5) = (456115123/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 11 5 h = (logRoundedQ ((endpointMeanCutoff 11 5:ℚ)/200)).2+(456115123/1000000000000000:ℚ)+((endpointMeanRuns 11 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 11 5).map (fun r => endpointRunWeightQ (endpointMeanCutoff 11 5) r*endpointJoint24Q (endpointMeanCornerK 11 5 h) (endpointMeanCornerA 11 5 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 11 5).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 11 5 h≤endpointMeanCorner 11 5 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 11 5 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint11_05

namespace EndpointAnalyticJoint11_06
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 1161 (.leaf (140819847400000:ℤ)) (.leaf (10203725600000:ℤ))) (.branch 1785 (.leaf (4252632100000:ℤ)) (.branch 2417 (.leaf (4152536100000:ℤ)) (.leaf (5074970900000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 148 (.leaf (1806445011741869:ℤ)) (.leaf (2176031039779914:ℤ))) (.branch 178 (.leaf (2393157932067155:ℤ)) (.branch 200 (.leaf (2576269818310042:ℤ)) (.leaf (2924798597940690:ℤ))))), (.branch 165 (.branch 148 (.leaf (1812887668056220:ℤ)) (.leaf (2189674769551740:ℤ))) (.branch 178 (.leaf (2412224711058242:ℤ)) (.branch 200 (.leaf (2600576029260917:ℤ)) (.leaf (2960712335868302:ℤ))))), (.branch 165 (.branch 148 (.leaf (1808042197485646:ℤ)) (.leaf (2179688173247484:ℤ))) (.branch 178 (.leaf (2398477526668375:ℤ)) (.branch 200 (.leaf (2583265668388140:ℤ)) (.leaf (2935706734522691:ℤ))))), (.branch 165 (.branch 148 (.leaf (1814757834899843:ℤ)) (.leaf (2193968778251908:ℤ))) (.branch 178 (.leaf (2418481508831293:ℤ)) (.branch 200 (.leaf (2608816721307986:ℤ)) (.leaf (2973598759962250:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 11 6) 8000 (endpointMeanRuns 11 6) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 11 6, EndpointRunConditions (endpointMeanCutoff 11 6) (endpointMeanBox 11 6).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 6, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 11 6 h) (endpointMeanCornerA 11 6 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 6, endpointJoint24Q (endpointMeanCornerK 11 6 h) (endpointMeanCornerA 11 6 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 11 6, endpointRunWeightQ (endpointMeanCutoff 11 6) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 11 6) = (45480249/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 11 6 h = (logRoundedQ ((endpointMeanCutoff 11 6:ℚ)/200)).2+(45480249/100000000000000:ℚ)+((endpointMeanRuns 11 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 11 6).map (fun r => endpointRunWeightQ (endpointMeanCutoff 11 6) r*endpointJoint24Q (endpointMeanCornerK 11 6 h) (endpointMeanCornerA 11 6 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 11 6).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 11 6 h≤endpointMeanCorner 11 6 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 11 6 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint11_06

namespace EndpointAnalyticJoint11_07
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 1161 (.leaf (136131402300000:ℤ)) (.leaf (10137022600000:ℤ))) (.branch 1785 (.leaf (4227548600000:ℤ)) (.branch 2417 (.leaf (4130108200000:ℤ)) (.leaf (5050731500000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 148 (.leaf (1812887668056220:ℤ)) (.leaf (2189674769551740:ℤ))) (.branch 178 (.leaf (2412224711058242:ℤ)) (.branch 200 (.leaf (2600576029260917:ℤ)) (.leaf (2960712335868302:ℤ))))), (.branch 165 (.branch 148 (.leaf (1819353301997962:ℤ)) (.leaf (2203404045604246:ℤ))) (.branch 178 (.leaf (2431443398979456:ℤ)) (.branch 200 (.leaf (2625111560870125:ℤ)) (.leaf (2997067060253181:ℤ))))), (.branch 165 (.branch 148 (.leaf (1814757834899843:ℤ)) (.leaf (2193968778251908:ℤ))) (.branch 178 (.leaf (2418481508831293:ℤ)) (.branch 200 (.leaf (2608816721307986:ℤ)) (.leaf (2973598759962250:ℤ))))), (.branch 165 (.branch 148 (.leaf (1821498416303695:ℤ)) (.leaf (2208342945116146:ℤ))) (.branch 178 (.leaf (2438652329873427:ℤ)) (.branch 200 (.leaf (2634620499417233:ℤ)) (.leaf (3011979868856579:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 11 7) 8000 (endpointMeanRuns 11 7) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 11 7, EndpointRunConditions (endpointMeanCutoff 11 7) (endpointMeanBox 11 7).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 7, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 11 7 h) (endpointMeanCornerA 11 7 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 7, endpointJoint24Q (endpointMeanCornerK 11 7 h) (endpointMeanCornerA 11 7 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 11 7, endpointRunWeightQ (endpointMeanCutoff 11 7) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 11 7) = (453246837/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 11 7 h = (logRoundedQ ((endpointMeanCutoff 11 7:ℚ)/200)).2+(453246837/1000000000000000:ℚ)+((endpointMeanRuns 11 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 11 7).map (fun r => endpointRunWeightQ (endpointMeanCutoff 11 7) r*endpointJoint24Q (endpointMeanCornerK 11 7 h) (endpointMeanCornerA 11 7 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 11 7).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 11 7 h≤endpointMeanCorner 11 7 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 11 7 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint11_07

namespace EndpointAnalyticJoint11_08
private noncomputable def weights : IntegerLookupTree := (.branch 1785 (.branch 1161 (.leaf (132345617000000:ℤ)) (.branch 1488 (.leaf (10082117200000:ℤ)) (.leaf (4206901500000:ℤ)))) (.branch 2417 (.leaf (4111647100000:ℤ)) (.branch 3626 (.leaf (1426039200000:ℤ)) (.leaf (181350400000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 132 (.leaf (1819353301997962:ℤ)) (.branch 148 (.leaf (2011758149281301:ℤ)) (.leaf (2203404045604246:ℤ)))) (.branch 178 (.leaf (2431443398979456:ℤ)) (.branch 200 (.leaf (2625111560870125:ℤ)) (.leaf (2997067060253181:ℤ))))), (.branch 165 (.branch 132 (.leaf (1825841995516429:ℤ)) (.branch 148 (.leaf (2021591699116664:ℤ)) (.leaf (2217219404313199:ℤ)))) (.branch 178 (.leaf (2450815206120335:ℤ)) (.branch 200 (.leaf (2649878576698435:ℤ)) (.leaf (3033868185988537:ℤ))))), (.branch 165 (.branch 132 (.leaf (1821498416303695:ℤ)) (.branch 148 (.leaf (2015145433586831:ℤ)) (.leaf (2208342945116146:ℤ)))) (.branch 178 (.leaf (2438652329873427:ℤ)) (.branch 200 (.leaf (2634620499417233:ℤ)) (.leaf (3011979868856579:ℤ))))), (.branch 165 (.branch 132 (.leaf (1828264034347033:ℤ)) (.branch 148 (.leaf (2025421423557676:ℤ)) (.leaf (2222811286826937:ℤ)))) (.branch 178 (.leaf (2458991381278303:ℤ)) (.branch 200 (.leaf (2660679502418013:ℤ)) (.leaf (3050856373948876:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 11 8) 8000 (endpointMeanRuns 11 8) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 11 8, EndpointRunConditions (endpointMeanCutoff 11 8) (endpointMeanBox 11 8).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 8, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 11 8 h) (endpointMeanCornerA 11 8 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 8, endpointJoint24Q (endpointMeanCornerK 11 8 h) (endpointMeanCornerA 11 8 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 11 8, endpointRunWeightQ (endpointMeanCutoff 11 8) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 11 8) = (451966327/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 11 8 h = (logRoundedQ ((endpointMeanCutoff 11 8:ℚ)/200)).2+(451966327/1000000000000000:ℚ)+((endpointMeanRuns 11 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 11 8).map (fun r => endpointRunWeightQ (endpointMeanCutoff 11 8) r*endpointJoint24Q (endpointMeanCornerK 11 8 h) (endpointMeanCornerA 11 8 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 11 8).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 11 8 h≤endpointMeanCorner 11 8 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 11 8 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint11_08

namespace EndpointAnalyticJoint11_09
private noncomputable def weights : IntegerLookupTree := (.branch 1785 (.branch 1304 (.branch 1161 (.leaf (128666494600000:ℤ)) (.leaf (4295808700000:ℤ))) (.branch 1488 (.leaf (4012236400000:ℤ)) (.leaf (4186481500000:ℤ)))) (.branch 2417 (.branch 2072 (.leaf (1991823500000:ℤ)) (.leaf (1178847000000:ℤ))) (.branch 3626 (.leaf (1420399600000:ℤ)) (.leaf (180721200000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 148 (.branch 132 (.leaf (1825841995516429:ℤ)) (.leaf (2021591699116664:ℤ))) (.branch 156 (.leaf (2217219404313199:ℤ)) (.leaf (2323612742950830:ℤ)))) (.branch 189 (.branch 178 (.leaf (2450815206120335:ℤ)) (.leaf (2649878576698435:ℤ))) (.branch 200 (.leaf (2833922576921806:ℤ)) (.leaf (3033868185988537:ℤ))))), (.branch 165 (.branch 148 (.branch 132 (.leaf (1832353830853211:ℤ)) (.leaf (2031473315715124:ℤ))) (.branch 156 (.leaf (2231121385417458:ℤ)) (.leaf (2339967122788701:ℤ)))) (.branch 189 (.branch 178 (.leaf (2470341352413036:ℤ)) (.leaf (2674879260719056:ℤ))) (.branch 200 (.leaf (2864523514940115:ℤ)) (.leaf (3071121194457298:ℤ))))), (.branch 165 (.branch 148 (.branch 132 (.leaf (1828264034347033:ℤ)) (.leaf (2025421423557676:ℤ))) (.branch 156 (.leaf (2222811286826937:ℤ)) (.leaf (2330316028414704:ℤ)))) (.branch 189 (.branch 178 (.leaf (2458991381278303:ℤ)) (.leaf (2660679502418013:ℤ))) (.branch 200 (.leaf (2847502561544177:ℤ)) (.leaf (3050856373948876:ℤ))))), (.branch 165 (.branch 148 (.branch 132 (.leaf (1835054782023809:ℤ)) (.leaf (2035749814694269:ℤ))) (.branch 156 (.leaf (2237374420387118:ℤ)) (.leaf (2347468841063508:ℤ)))) (.branch 189 (.branch 178 (.leaf (2479500066134809:ℤ)) (.leaf (2686996254736970:ℤ))) (.branch 200 (.leaf (2879779372234461:ℤ)) (.leaf (3090234669462753:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 11 9) 8000 (endpointMeanRuns 11 9) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 11 9, EndpointRunConditions (endpointMeanCutoff 11 9) (endpointMeanBox 11 9).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 9, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 11 9 h) (endpointMeanCornerA 11 9 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 9, endpointJoint24Q (endpointMeanCornerK 11 9 h) (endpointMeanCornerA 11 9 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 11 9, endpointRunWeightQ (endpointMeanCutoff 11 9) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 11 9) = (90139981/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 11 9 h = (logRoundedQ ((endpointMeanCutoff 11 9:ℚ)/200)).2+(90139981/200000000000000:ℚ)+((endpointMeanRuns 11 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 11 9).map (fun r => endpointRunWeightQ (endpointMeanCutoff 11 9) r*endpointJoint24Q (endpointMeanCornerK 11 9 h) (endpointMeanCornerA 11 9 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 11 9).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 11 9 h≤endpointMeanCorner 11 9 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 11 9 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint11_09

namespace EndpointAnalyticJoint11_10
private noncomputable def weights : IntegerLookupTree := (.branch 1488 (.branch 1161 (.leaf (125090811700000:ℤ)) (.branch 1304 (.leaf (4272250800000:ℤ)) (.leaf (3991508700000:ℤ)))) (.branch 2417 (.branch 1785 (.leaf (4166283800000:ℤ)) (.leaf (4075329600000:ℤ))) (.branch 3626 (.leaf (1414821500000:ℤ)) (.leaf (180098800000:ℤ)))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 132 (.leaf (1832353830853211:ℤ)) (.branch 148 (.leaf (2031473315715124:ℤ)) (.leaf (2231121385417458:ℤ)))) (.branch 189 (.branch 178 (.leaf (2470341352413036:ℤ)) (.leaf (2674879260719056:ℤ))) (.branch 200 (.leaf (2864523514940115:ℤ)) (.leaf (3071121194457298:ℤ))))), (.branch 165 (.branch 132 (.leaf (1838888890543234:ℤ)) (.branch 148 (.leaf (2041403234028828:ℤ)) (.leaf (2245110532040043:ℤ)))) (.branch 189 (.branch 178 (.leaf (2490023067509170:ℤ)) (.leaf (2700115817510221:ℤ))) (.branch 200 (.leaf (2895454884500634:ℤ)) (.leaf (3108831634348551:ℤ))))), (.branch 165 (.branch 132 (.leaf (1835054782023809:ℤ)) (.branch 148 (.leaf (2035749814694269:ℤ)) (.leaf (2237374420387118:ℤ)))) (.branch 189 (.branch 178 (.leaf (2479500066134809:ℤ)) (.leaf (2686996254736970:ℤ))) (.branch 200 (.leaf (2879779372234461:ℤ)) (.leaf (3090234669462753:ℤ))))), (.branch 165 (.branch 132 (.leaf (1841870752673384:ℤ)) (.branch 148 (.leaf (2046130874210011:ℤ)) (.leaf (2252032966841931:ℤ)))) (.branch 189 (.branch 178 (.leaf (2500179799234004:ℤ)) (.leaf (2713573305769844:ℤ))) (.branch 200 (.leaf (2912422044758339:ℤ)) (.leaf (3130121232153945:ℤ)))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 11 10) 8000 (endpointMeanRuns 11 10) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 11 10, EndpointRunConditions (endpointMeanCutoff 11 10) (endpointMeanBox 11 10).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 10, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 11 10 h) (endpointMeanCornerA 11 10 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 10, endpointJoint24Q (endpointMeanCornerK 11 10 h) (endpointMeanCornerA 11 10 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 11 10, endpointRunWeightQ (endpointMeanCutoff 11 10) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 11 10) = (14045227/31250000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 11 10 h = (logRoundedQ ((endpointMeanCutoff 11 10:ℚ)/200)).2+(14045227/31250000000000:ℚ)+((endpointMeanRuns 11 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 11 10).map (fun r => endpointRunWeightQ (endpointMeanCutoff 11 10) r*endpointJoint24Q (endpointMeanCornerK 11 10 h) (endpointMeanCornerA 11 10 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 11 10).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 11 10 h≤endpointMeanCorner 11 10 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 11 10 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint11_10

namespace EndpointAnalyticJoint11_11
private noncomputable def weights : IntegerLookupTree := (.branch 1785 (.branch 1304 (.branch 1161 (.leaf (121615454800000:ℤ)) (.leaf (4248946500000:ℤ))) (.branch 1488 (.leaf (3971004200000:ℤ)) (.branch 1658 (.leaf (2404756100000:ℤ)) (.leaf (1222803600000:ℤ))))) (.branch 2417 (.branch 2072 (.leaf (1974042200000:ℤ)) (.leaf (1168934000000:ℤ))) (.branch 2901 (.leaf (672586800000:ℤ)) (.branch 3626 (.leaf (278716800000:ℤ)) (.leaf (179483200000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 140 (.branch 132 (.leaf (1838888890543234:ℤ)) (.leaf (2041403234028828:ℤ))) (.branch 148 (.leaf (2140250154006023:ℤ)) (.branch 156 (.leaf (2245110532040043:ℤ)) (.leaf (2356436610335760:ℤ))))) (.branch 178 (.branch 170 (.leaf (2490023067509170:ℤ)) (.leaf (2568324984680934:ℤ))) (.branch 189 (.leaf (2700115817510221:ℤ)) (.branch 200 (.leaf (2895454884500634:ℤ)) (.leaf (3108831634348551:ℤ)))))), (.branch 165 (.branch 140 (.branch 132 (.leaf (1845447257415761:ℤ)) (.leaf (2051381690158395:ℤ))) (.branch 148 (.leaf (2152136662966362:ℤ)) (.branch 156 (.leaf (2259187390709364:ℤ)) (.leaf (2373022015759366:ℤ))))) (.branch 178 (.branch 170 (.leaf (2509861590857223:ℤ)) (.leaf (2590190847891140:ℤ))) (.branch 189 (.leaf (2725590472449603:ℤ)) (.branch 200 (.leaf (2926720253631379:ℤ)) (.leaf (3147005122483997:ℤ)))))), (.branch 165 (.branch 140 (.branch 132 (.leaf (1841870752673384:ℤ)) (.leaf (2046130874210011:ℤ))) (.branch 148 (.leaf (2145987194638574:ℤ)) (.branch 156 (.leaf (2252032966841931:ℤ)) (.leaf (2364747910828591:ℤ))))) (.branch 178 (.branch 170 (.leaf (2500179799234004:ℤ)) (.leaf (2579654754652388:ℤ))) (.branch 189 (.leaf (2713573305769844:ℤ)) (.branch 200 (.leaf (2912422044758339:ℤ)) (.leaf (3130121232153945:ℤ)))))), (.branch 165 (.branch 140 (.branch 132 (.leaf (1848712039981814:ℤ)) (.leaf (2056564870680922:ℤ))) (.branch 148 (.leaf (2158430777845796:ℤ)) (.branch 156 (.leaf (2266787551305497:ℤ)) (.leaf (2382154167053712:ℤ))))) (.branch 178 (.branch 170 (.leaf (2521032007166691:ℤ)) (.leaf (2602658319825925:ℤ))) (.branch 189 (.leaf (2740413230128409:ℤ)) (.branch 200 (.leaf (2945434726207126:ℤ)) (.leaf (3170522622375566:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 11 11) 8000 (endpointMeanRuns 11 11) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 11 11, EndpointRunConditions (endpointMeanCutoff 11 11) (endpointMeanBox 11 11).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 11, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 11 11 h) (endpointMeanCornerA 11 11 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 11, endpointJoint24Q (endpointMeanCornerK 11 11 h) (endpointMeanCornerA 11 11 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 11 11, endpointRunWeightQ (endpointMeanCutoff 11 11) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 11 11) = (224104053/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 11 11 h = (logRoundedQ ((endpointMeanCutoff 11 11:ℚ)/200)).2+(224104053/500000000000000:ℚ)+((endpointMeanRuns 11 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 11 11).map (fun r => endpointRunWeightQ (endpointMeanCutoff 11 11) r*endpointJoint24Q (endpointMeanCornerK 11 11 h) (endpointMeanCornerA 11 11 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 11 11).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 11 11 h≤endpointMeanCorner 11 11 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 11 11 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint11_11

namespace EndpointAnalyticJoint11_12
private noncomputable def weights : IntegerLookupTree := (.branch 1658 (.branch 1304 (.branch 1161 (.leaf (118237415400000:ℤ)) (.branch 1222 (.leaf (1776443700000:ℤ)) (.leaf (2102593200000:ℤ)))) (.branch 1398 (.leaf (2016053500000:ℤ)) (.branch 1488 (.leaf (1564990000000:ℤ)) (.leaf (2393151200000:ℤ))))) (.branch 2072 (.branch 1785 (.leaf (1217143100000:ℤ)) (.branch 1902 (.leaf (837879000000:ℤ)) (.leaf (910972000000:ℤ)))) (.branch 2901 (.branch 2417 (.leaf (1164056900000:ℤ)) (.leaf (669946500000:ℤ))) (.branch 3626 (.leaf (277693600000:ℤ)) (.leaf (178874000000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 148 (.branch 132 (.leaf (1845447257415761:ℤ)) (.branch 140 (.leaf (2051381690158395:ℤ)) (.leaf (2152136662966362:ℤ)))) (.branch 156 (.leaf (2259187390709364:ℤ)) (.branch 161 (.leaf (2373022015759366:ℤ)) (.leaf (2447848791253763:ℤ))))) (.branch 183 (.branch 170 (.leaf (2509861590857223:ℤ)) (.branch 178 (.leaf (2590190847891140:ℤ)) (.leaf (2725590472449603:ℤ)))) (.branch 195 (.branch 189 (.leaf (2814772670154601:ℤ)) (.leaf (2926720253631379:ℤ))) (.branch 200 (.leaf (3044361901790125:ℤ)) (.leaf (3147005122483997:ℤ)))))), (.branch 165 (.branch 148 (.branch 132 (.leaf (1852029014595478:ℤ)) (.branch 140 (.leaf (2061408921358491:ℤ)) (.leaf (2164089187151605:ℤ)))) (.branch 156 (.leaf (2273352511380563:ℤ)) (.branch 161 (.leaf (2389724154929110:ℤ)) (.leaf (2466319752243926:ℤ))))) (.branch 183 (.branch 170 (.leaf (2529858171780633:ℤ)) (.branch 178 (.leaf (2612242869775494:ℤ)) (.leaf (2751305471910531:ℤ)))) (.branch 195 (.branch 189 (.leaf (2843033531107511:ℤ)) (.leaf (2958323228888233:ℤ))) (.branch 200 (.leaf (3079648909505721:ℤ)) (.leaf (3185647344654546:ℤ)))))), (.branch 165 (.branch 148 (.branch 132 (.leaf (1848712039981814:ℤ)) (.branch 140 (.leaf (2056564870680922:ℤ)) (.leaf (2158430777845796:ℤ)))) (.branch 156 (.leaf (2266787551305497:ℤ)) (.branch 161 (.leaf (2382154167053712:ℤ)) (.leaf (2458068821634357:ℤ))))) (.branch 183 (.branch 170 (.leaf (2521032007166691:ℤ)) (.branch 178 (.leaf (2602658319825925:ℤ)) (.leaf (2740413230128409:ℤ)))) (.branch 195 (.branch 189 (.leaf (2831262974801709:ℤ)) (.leaf (2945434726207126:ℤ))) (.branch 200 (.leaf (3065570991632833:ℤ)) (.leaf (3170522622375566:ℤ)))))), (.branch 165 (.branch 148 (.branch 132 (.leaf (1855578737983134:ℤ)) (.branch 140 (.leaf (2067052074052584:ℤ)) (.leaf (2170946515613596:ℤ)))) (.branch 156 (.leaf (2281638802987481:ℤ)) (.branch 161 (.leaf (2399688545923277:ℤ)) (.leaf (2477476934705995:ℤ))))) (.branch 183 (.branch 170 (.leaf (2542058128421849:ℤ)) (.branch 178 (.leaf (2625867014778844:ℤ)) (.leaf (2767518627889903:ℤ)))) (.branch 195 (.branch 189 (.leaf (2861081787511709:ℤ)) (.leaf (2978821610679960:ℤ))) (.branch 200 (.leaf (3102898475408352:ℤ)) (.leaf (3211445485157119:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 11 12) 8000 (endpointMeanRuns 11 12) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 11 12, EndpointRunConditions (endpointMeanCutoff 11 12) (endpointMeanBox 11 12).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 12, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 11 12 h) (endpointMeanCornerA 11 12 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 12, endpointJoint24Q (endpointMeanCornerK 11 12 h) (endpointMeanCornerA 11 12 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 11 12, endpointRunWeightQ (endpointMeanCutoff 11 12) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 11 12) = (223491073/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 11 12 h = (logRoundedQ ((endpointMeanCutoff 11 12:ℚ)/200)).2+(223491073/500000000000000:ℚ)+((endpointMeanRuns 11 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 11 12).map (fun r => endpointRunWeightQ (endpointMeanCutoff 11 12) r*endpointJoint24Q (endpointMeanCornerK 11 12 h) (endpointMeanCornerA 11 12 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 11 12).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 11 12 h≤endpointMeanCorner 11 12 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 11 12 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint11_12

namespace EndpointAnalyticJoint11_13
private noncomputable def weights : IntegerLookupTree := (.branch 1658 (.branch 1304 (.branch 1161 (.leaf (114308140800000:ℤ)) (.branch 1222 (.leaf (1764779500000:ℤ)) (.leaf (2089187600000:ℤ)))) (.branch 1488 (.branch 1398 (.leaf (2003620100000:ℤ)) (.leaf (1555641300000:ℤ))) (.branch 1568 (.leaf (1132114300000:ℤ)) (.leaf (1060789600000:ℤ))))) (.branch 2072 (.branch 1785 (.leaf (1210429200000:ℤ)) (.branch 1902 (.leaf (833392900000:ℤ)) (.leaf (906240200000:ℤ)))) (.branch 2901 (.branch 2417 (.leaf (1158272000000:ℤ)) (.leaf (666814800000:ℤ))) (.branch 3626 (.leaf (276479900000:ℤ)) (.leaf (178151600000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 170 (.branch 148 (.branch 132 (.leaf (1852029014595478:ℤ)) (.branch 140 (.leaf (2061408921358491:ℤ)) (.leaf (2164089187151605:ℤ)))) (.branch 161 (.branch 156 (.leaf (2273352511380563:ℤ)) (.leaf (2389724154929110:ℤ))) (.branch 165 (.leaf (2466319752243926:ℤ)) (.leaf (2529858171780633:ℤ))))) (.branch 183 (.branch 174 (.leaf (2612242869775494:ℤ)) (.branch 178 (.leaf (2680625171649332:ℤ)) (.leaf (2751305471910531:ℤ)))) (.branch 195 (.branch 189 (.leaf (2843033531107511:ℤ)) (.leaf (2958323228888233:ℤ))) (.branch 200 (.leaf (3079648909505721:ℤ)) (.leaf (3185647344654546:ℤ)))))), (.branch 170 (.branch 148 (.branch 132 (.leaf (1858634245503523:ℤ)) (.branch 140 (.leaf (2071485166043515:ℤ)) (.leaf (2176108093196724:ℤ)))) (.branch 161 (.branch 156 (.leaf (2287606447457006:ℤ)) (.leaf (2406543849456959:ℤ))) (.branch 165 (.leaf (2484930091287639:ℤ)) (.leaf (2550014069556453:ℤ))))) (.branch 183 (.branch 174 (.leaf (2634482635226925:ℤ)) (.branch 178 (.leaf (2704662042731442:ℤ)) (.leaf (2777263083460091:ℤ)))) (.branch 195 (.branch 189 (.leaf (2871578136559677:ℤ)) (.leaf (2990267455770980:ℤ))) (.branch 200 (.leaf (3115344926712855:ℤ)) (.leaf (3224764056467202:ℤ)))))), (.branch 170 (.branch 148 (.branch 132 (.leaf (1855578737983134:ℤ)) (.branch 140 (.leaf (2067052074052584:ℤ)) (.leaf (2170946515613596:ℤ)))) (.branch 161 (.branch 156 (.leaf (2281638802987481:ℤ)) (.leaf (2399688545923277:ℤ))) (.branch 165 (.leaf (2477476934705995:ℤ)) (.leaf (2542058128421849:ℤ))))) (.branch 183 (.branch 174 (.leaf (2625867014778844:ℤ)) (.branch 178 (.leaf (2695493370542554:ℤ)) (.leaf (2767518627889903:ℤ)))) (.branch 195 (.branch 189 (.leaf (2861081787511709:ℤ)) (.leaf (2978821610679960:ℤ))) (.branch 200 (.leaf (3102898475408352:ℤ)) (.leaf (3211445485157119:ℤ)))))), (.branch 170 (.branch 148 (.branch 132 (.leaf (1862470941060643:ℤ)) (.branch 140 (.leaf (2077592755647146:ℤ)) (.leaf (2183534826332761:ℤ)))) (.branch 161 (.branch 156 (.leaf (2296587355219926:ℤ)) (.leaf (2417351990512684:ℤ))) (.branch 165 (.leaf (2497038287934979:ℤ)) (.leaf (2563259613485875:ℤ))))) (.branch 183 (.branch 174 (.leaf (2649282668715698:ℤ)) (.branch 178 (.leaf (2720820966795604:ℤ)) (.leaf (2794892124848892:ℤ)))) (.branch 195 (.branch 189 (.leaf (2891214651441729:ℤ)) (.leaf (3012586939816623:ℤ))) (.branch 200 (.leaf (3140680471915372:ℤ)) (.leaf (3252896551297456:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 11 13) 8000 (endpointMeanRuns 11 13) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 11 13, EndpointRunConditions (endpointMeanCutoff 11 13) (endpointMeanBox 11 13).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 13, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 11 13 h) (endpointMeanCornerA 11 13 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 13, endpointJoint24Q (endpointMeanCornerK 11 13 h) (endpointMeanCornerA 11 13 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 11 13, endpointRunWeightQ (endpointMeanCutoff 11 13) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 11 13) = (222764011/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 11 13 h = (logRoundedQ ((endpointMeanCutoff 11 13:ℚ)/200)).2+(222764011/500000000000000:ℚ)+((endpointMeanRuns 11 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 11 13).map (fun r => endpointRunWeightQ (endpointMeanCutoff 11 13) r*endpointJoint24Q (endpointMeanCornerK 11 13 h) (endpointMeanCornerA 11 13 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 11 13).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 11 13 h≤endpointMeanCorner 11 13 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 11 13 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint11_13

namespace EndpointAnalyticJoint11_14
private noncomputable def weights : IntegerLookupTree := (.branch 1658 (.branch 1304 (.branch 1161 (.leaf (111134102800000:ℤ)) (.branch 1222 (.leaf (1755170700000:ℤ)) (.leaf (2078144300000:ℤ)))) (.branch 1488 (.branch 1398 (.leaf (1993377500000:ℤ)) (.leaf (1547939900000:ℤ))) (.branch 1568 (.leaf (1126659800000:ℤ)) (.leaf (1055803200000:ℤ))))) (.branch 2072 (.branch 1785 (.leaf (1204898300000:ℤ)) (.branch 1902 (.leaf (829697300000:ℤ)) (.leaf (902342200000:ℤ)))) (.branch 2901 (.branch 2417 (.leaf (1153506500000:ℤ)) (.leaf (664235000000:ℤ))) (.branch 3626 (.leaf (275480100000:ℤ)) (.leaf (177556400000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 170 (.branch 148 (.branch 132 (.leaf (1858634245503523:ℤ)) (.branch 140 (.leaf (2071485166043515:ℤ)) (.leaf (2176108093196724:ℤ)))) (.branch 161 (.branch 156 (.leaf (2287606447457006:ℤ)) (.leaf (2406543849456959:ℤ))) (.branch 165 (.leaf (2484930091287639:ℤ)) (.leaf (2550014069556453:ℤ))))) (.branch 183 (.branch 174 (.leaf (2634482635226925:ℤ)) (.branch 178 (.leaf (2704662042731442:ℤ)) (.leaf (2777263083460091:ℤ)))) (.branch 195 (.branch 189 (.leaf (2871578136559677:ℤ)) (.leaf (2990267455770980:ℤ))) (.branch 200 (.leaf (3115344926712855:ℤ)) (.leaf (3224764056467202:ℤ)))))), (.branch 170 (.branch 148 (.branch 132 (.leaf (1865263033858567:ℤ)) (.branch 140 (.leaf (2081610663793224:ℤ)) (.leaf (2188193749772915:ℤ)))) (.branch 161 (.branch 156 (.leaf (2301949755811905:ℤ)) (.leaf (2423481926737652:ℤ))) (.branch 165 (.leaf (2503680860102879:ℤ)) (.leaf (2570330553494637:ℤ))))) (.branch 183 (.branch 174 (.leaf (2656911742631611:ℤ)) (.branch 178 (.leaf (2728914449792819:ℤ)) (.leaf (2803465596059077:ℤ)))) (.branch 195 (.branch 189 (.leaf (2900409335360638:ℤ)) (.leaf (3022556619143820:ℤ))) (.branch 200 (.leaf (3151454694214877:ℤ)) (.leaf (3264361084202336:ℤ)))))), (.branch 170 (.branch 148 (.branch 132 (.leaf (1862470941060643:ℤ)) (.branch 140 (.leaf (2077592755647146:ℤ)) (.leaf (2183534826332761:ℤ)))) (.branch 161 (.branch 156 (.leaf (2296587355219926:ℤ)) (.leaf (2417351990512684:ℤ))) (.branch 165 (.leaf (2497038287934979:ℤ)) (.leaf (2563259613485875:ℤ))))) (.branch 183 (.branch 174 (.leaf (2649282668715698:ℤ)) (.branch 178 (.leaf (2720820966795604:ℤ)) (.leaf (2794892124848892:ℤ)))) (.branch 195 (.branch 189 (.leaf (2891214651441729:ℤ)) (.leaf (3012586939816623:ℤ))) (.branch 200 (.leaf (3140680471915372:ℤ)) (.leaf (3252896551297456:ℤ)))))), (.branch 170 (.branch 148 (.branch 132 (.leaf (1869388743948226:ℤ)) (.branch 140 (.leaf (2088187188170321:ℤ)) (.leaf (2196196130820140:ℤ)))) (.branch 161 (.branch 156 (.leaf (2311633845484262:ℤ)) (.leaf (2435145450839045:ℤ))) (.branch 165 (.leaf (2516754091255826:ℤ)) (.leaf (2584637924942611:ℤ))))) (.branch 183 (.branch 174 (.leaf (2672907127152634:ℤ)) (.branch 178 (.leaf (2746386548101401:ℤ)) (.leaf (2822536372771656:ℤ)))) (.branch 195 (.branch 189 (.leaf (2921664874173789:ℤ)) (.leaf (3046735003336452:ℤ))) (.branch 200 (.leaf (3178922515462724:ℤ)) (.leaf (3294882638471815:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 11 14) 8000 (endpointMeanRuns 11 14) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 11 14, EndpointRunConditions (endpointMeanCutoff 11 14) (endpointMeanBox 11 14).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 14, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 11 14 h) (endpointMeanCornerA 11 14 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 14, endpointJoint24Q (endpointMeanCornerK 11 14 h) (endpointMeanCornerA 11 14 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 11 14, endpointRunWeightQ (endpointMeanCutoff 11 14) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 11 14) = (27770633/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 11 14 h = (logRoundedQ ((endpointMeanCutoff 11 14:ℚ)/200)).2+(27770633/62500000000000:ℚ)+((endpointMeanRuns 11 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 11 14).map (fun r => endpointRunWeightQ (endpointMeanCutoff 11 14) r*endpointJoint24Q (endpointMeanCornerK 11 14 h) (endpointMeanCornerA 11 14 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 11 14).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 11 14 h≤endpointMeanCorner 11 14 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 11 14 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint11_14

namespace EndpointAnalyticJoint11_15
private noncomputable def weights : IntegerLookupTree := (.branch 1658 (.branch 1304 (.branch 1161 (.leaf (108048415100000:ℤ)) (.branch 1222 (.leaf (1745660900000:ℤ)) (.leaf (2067214700000:ℤ)))) (.branch 1398 (.leaf (1983240400000:ℤ)) (.branch 1488 (.leaf (1540317900000:ℤ)) (.leaf (2356824800000:ℤ))))) (.branch 2417 (.branch 1785 (.leaf (1199424400000:ℤ)) (.branch 2072 (.leaf (1937909000000:ℤ)) (.leaf (1148790100000:ℤ)))) (.branch 2901 (.leaf (661681700000:ℤ)) (.branch 3626 (.leaf (274490600000:ℤ)) (.leaf (176967400000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 170 (.branch 148 (.branch 132 (.leaf (1865263033858567:ℤ)) (.branch 140 (.leaf (2081610663793224:ℤ)) (.leaf (2188193749772915:ℤ)))) (.branch 156 (.leaf (2301949755811905:ℤ)) (.branch 165 (.leaf (2423481926737652:ℤ)) (.leaf (2570330553494637:ℤ))))) (.branch 189 (.branch 178 (.leaf (2656911742631611:ℤ)) (.branch 183 (.leaf (2803465596059077:ℤ)) (.leaf (2900409335360638:ℤ)))) (.branch 195 (.leaf (3022556619143820:ℤ)) (.branch 200 (.leaf (3151454694214877:ℤ)) (.leaf (3264361084202336:ℤ)))))), (.branch 170 (.branch 148 (.branch 132 (.leaf (1871915463677856:ℤ)) (.branch 140 (.leaf (2091785655358460:ℤ)) (.leaf (2200346527598888:ℤ)))) (.branch 156 (.leaf (2316382996810065:ℤ)) (.branch 165 (.leaf (2440539219989433:ℤ)) (.leaf (2590808903018014:ℤ))))) (.branch 189 (.branch 178 (.leaf (2679531803983852:ℤ)) (.branch 183 (.leaf (2829915320263827:ℤ)) (.leaf (2929530004962938:ℤ)))) (.branch 195 (.leaf (3055194443660437:ℤ)) (.branch 200 (.leaf (3187983007765487:ℤ)) (.leaf (3304444325681487:ℤ)))))), (.branch 170 (.branch 148 (.branch 132 (.leaf (1869388743948226:ℤ)) (.branch 140 (.leaf (2088187188170321:ℤ)) (.leaf (2196196130820140:ℤ)))) (.branch 156 (.leaf (2311633845484262:ℤ)) (.branch 165 (.leaf (2435145450839045:ℤ)) (.leaf (2584637924942611:ℤ))))) (.branch 189 (.branch 178 (.leaf (2672907127152634:ℤ)) (.branch 183 (.leaf (2822536372771656:ℤ)) (.leaf (2921664874173789:ℤ)))) (.branch 195 (.leaf (3046735003336452:ℤ)) (.branch 200 (.leaf (3178922515462724:ℤ)) (.leaf (3294882638471815:ℤ)))))), (.branch 170 (.branch 148 (.branch 132 (.leaf (1876332241731625:ℤ)) (.branch 140 (.leaf (2098835645718463:ℤ)) (.leaf (2208930852332696:ℤ)))) (.branch 156 (.leaf (2326778915438484:ℤ)) (.branch 165 (.leaf (2453069883912288:ℤ)) (.leaf (2606194537574277:ℤ))))) (.branch 189 (.branch 178 (.leaf (2696742252062811:ℤ)) (.branch 183 (.leaf (2850454049653059:ℤ)) (.leaf (2952435798125305:ℤ)))) (.branch 195 (.leaf (3081270139583287:ℤ)) (.branch 200 (.leaf (3217630207746955:ℤ)) (.leaf (3337410652353160:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 11 15) 8000 (endpointMeanRuns 11 15) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 11 15, EndpointRunConditions (endpointMeanCutoff 11 15) (endpointMeanBox 11 15).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 15, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 11 15 h) (endpointMeanCornerA 11 15 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 15, endpointJoint24Q (endpointMeanCornerK 11 15 h) (endpointMeanCornerA 11 15 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 11 15, endpointRunWeightQ (endpointMeanCutoff 11 15) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 11 15) = (44314457/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 11 15 h = (logRoundedQ ((endpointMeanCutoff 11 15:ℚ)/200)).2+(44314457/100000000000000:ℚ)+((endpointMeanRuns 11 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 11 15).map (fun r => endpointRunWeightQ (endpointMeanCutoff 11 15) r*endpointJoint24Q (endpointMeanCornerK 11 15 h) (endpointMeanCornerA 11 15 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 11 15).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 11 15 h≤endpointMeanCorner 11 15 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 11 15 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint11_15

namespace EndpointAnalyticJoint11_16
private noncomputable def weights : IntegerLookupTree := (.branch 1658 (.branch 1304 (.branch 1161 (.leaf (105048467800000:ℤ)) (.leaf (4131649900000:ℤ))) (.branch 1488 (.leaf (3867799500000:ℤ)) (.leaf (2345716800000:ℤ)))) (.branch 2072 (.branch 1785 (.leaf (1194006300000:ℤ)) (.leaf (1929535100000:ℤ))) (.branch 2417 (.leaf (1144121700000:ℤ)) (.branch 3626 (.leaf (1381529300000:ℤ)) (.leaf (176384400000:ℤ))))))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 165 (.branch 148 (.branch 132 (.leaf (1871915463677856:ℤ)) (.leaf (2091785655358460:ℤ))) (.branch 156 (.leaf (2316382996810065:ℤ)) (.leaf (2440539219989433:ℤ)))) (.branch 178 (.branch 170 (.leaf (2590808903018014:ℤ)) (.leaf (2679531803983852:ℤ))) (.branch 189 (.leaf (2829915320263827:ℤ)) (.branch 200 (.leaf (3055194443660437:ℤ)) (.leaf (3304444325681487:ℤ)))))), (.branch 165 (.branch 148 (.branch 132 (.leaf (1878591619278276:ℤ)) (.leaf (2102010382666870:ℤ))) (.branch 156 (.leaf (2330906734329788:ℤ)) (.leaf (2457716568295004:ℤ)))) (.branch 178 (.branch 170 (.leaf (2611450407742822:ℤ)) (.leaf (2702344445001941:ℤ))) (.branch 189 (.leaf (2856614588429982:ℤ)) (.branch 200 (.leaf (3088184694193632:ℤ)) (.leaf (3345019751145809:ℤ)))))), (.branch 165 (.branch 148 (.branch 132 (.leaf (1876332241731625:ℤ)) (.leaf (2098835645718463:ℤ))) (.branch 156 (.leaf (2326778915438484:ℤ)) (.leaf (2453069883912288:ℤ)))) (.branch 178 (.branch 170 (.leaf (2606194537574277:ℤ)) (.leaf (2696742252062811:ℤ))) (.branch 189 (.leaf (2850454049653059:ℤ)) (.branch 200 (.leaf (3081270139583287:ℤ)) (.leaf (3337410652353160:ℤ)))))), (.branch 165 (.branch 148 (.branch 132 (.leaf (1883301529849766:ℤ)) (.leaf (2109538403785637:ℤ))) (.branch 156 (.leaf (2342023210944524:ℤ)) (.leaf (2471126253786636:ℤ)))) (.branch 178 (.branch 170 (.leaf (2627930938463198:ℤ)) (.leaf (2720789922023172:ℤ))) (.branch 189 (.leaf (2878647859975997:ℤ)) (.branch 200 (.leaf (3116196736076676:ℤ)) (.leaf (3380487587747997:ℤ))))))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 11 16) 8000 (endpointMeanRuns 11 16) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 11 16, EndpointRunConditions (endpointMeanCutoff 11 16) (endpointMeanBox 11 16).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 16, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 11 16 h) (endpointMeanCornerA 11 16 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 11 16, endpointJoint24Q (endpointMeanCornerK 11 16 h) (endpointMeanCornerA 11 16 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 11 16, endpointRunWeightQ (endpointMeanCutoff 11 16) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 11 16) = (220985549/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 11 16 h = (logRoundedQ ((endpointMeanCutoff 11 16:ℚ)/200)).2+(220985549/500000000000000:ℚ)+((endpointMeanRuns 11 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 11 16).map (fun r => endpointRunWeightQ (endpointMeanCutoff 11 16) r*endpointJoint24Q (endpointMeanCornerK 11 16 h) (endpointMeanCornerA 11 16 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 11 16).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 11 16 h≤endpointMeanCorner 11 16 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 11 16 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint11_16

private theorem activeIndices06 : ∀ai : Fin 42, endpointMeanActive 6 ai → ai∈
    ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow06 (ai : Fin 42) : endpointMeanActive 6 ai →
    EndpointJointNumericalConditions 6 ai := by
  intro hact
  have hi := activeIndices06 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint06_01.conditions
  · exact EndpointAnalyticJoint06_02.conditions
  · exact EndpointAnalyticJoint06_03.conditions
  · exact EndpointAnalyticJoint06_04.conditions
  · exact EndpointAnalyticJoint06_05.conditions
  · exact EndpointAnalyticJoint06_06.conditions
  · exact EndpointAnalyticJoint06_07.conditions
  · exact EndpointAnalyticJoint06_08.conditions
  · exact EndpointAnalyticJoint06_09.conditions
  · exact EndpointAnalyticJoint06_10.conditions
  · exact EndpointAnalyticJoint06_11.conditions
  · exact EndpointAnalyticJoint06_12.conditions
  · exact EndpointAnalyticJoint06_13.conditions

private theorem activeIndices07 : ∀ai : Fin 42, endpointMeanActive 7 ai → ai∈
    ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow07 (ai : Fin 42) : endpointMeanActive 7 ai →
    EndpointJointNumericalConditions 7 ai := by
  intro hact
  have hi := activeIndices07 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint07_01.conditions
  · exact EndpointAnalyticJoint07_02.conditions
  · exact EndpointAnalyticJoint07_03.conditions
  · exact EndpointAnalyticJoint07_04.conditions
  · exact EndpointAnalyticJoint07_05.conditions
  · exact EndpointAnalyticJoint07_06.conditions
  · exact EndpointAnalyticJoint07_07.conditions
  · exact EndpointAnalyticJoint07_08.conditions
  · exact EndpointAnalyticJoint07_09.conditions
  · exact EndpointAnalyticJoint07_10.conditions
  · exact EndpointAnalyticJoint07_11.conditions
  · exact EndpointAnalyticJoint07_12.conditions
  · exact EndpointAnalyticJoint07_13.conditions
  · exact EndpointAnalyticJoint07_14.conditions

private theorem activeIndices08 : ∀ai : Fin 42, endpointMeanActive 8 ai → ai∈
    ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow08 (ai : Fin 42) : endpointMeanActive 8 ai →
    EndpointJointNumericalConditions 8 ai := by
  intro hact
  have hi := activeIndices08 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint08_01.conditions
  · exact EndpointAnalyticJoint08_02.conditions
  · exact EndpointAnalyticJoint08_03.conditions
  · exact EndpointAnalyticJoint08_04.conditions
  · exact EndpointAnalyticJoint08_05.conditions
  · exact EndpointAnalyticJoint08_06.conditions
  · exact EndpointAnalyticJoint08_07.conditions
  · exact EndpointAnalyticJoint08_08.conditions
  · exact EndpointAnalyticJoint08_09.conditions
  · exact EndpointAnalyticJoint08_10.conditions
  · exact EndpointAnalyticJoint08_11.conditions
  · exact EndpointAnalyticJoint08_12.conditions
  · exact EndpointAnalyticJoint08_13.conditions
  · exact EndpointAnalyticJoint08_14.conditions

private theorem activeIndices09 : ∀ai : Fin 42, endpointMeanActive 9 ai → ai∈
    ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow09 (ai : Fin 42) : endpointMeanActive 9 ai →
    EndpointJointNumericalConditions 9 ai := by
  intro hact
  have hi := activeIndices09 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint09_01.conditions
  · exact EndpointAnalyticJoint09_02.conditions
  · exact EndpointAnalyticJoint09_03.conditions
  · exact EndpointAnalyticJoint09_04.conditions
  · exact EndpointAnalyticJoint09_05.conditions
  · exact EndpointAnalyticJoint09_06.conditions
  · exact EndpointAnalyticJoint09_07.conditions
  · exact EndpointAnalyticJoint09_08.conditions
  · exact EndpointAnalyticJoint09_09.conditions
  · exact EndpointAnalyticJoint09_10.conditions
  · exact EndpointAnalyticJoint09_11.conditions
  · exact EndpointAnalyticJoint09_12.conditions
  · exact EndpointAnalyticJoint09_13.conditions
  · exact EndpointAnalyticJoint09_14.conditions
  · exact EndpointAnalyticJoint09_15.conditions

private theorem activeIndices10 : ∀ai : Fin 42, endpointMeanActive 10 ai → ai∈
    ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow10 (ai : Fin 42) : endpointMeanActive 10 ai →
    EndpointJointNumericalConditions 10 ai := by
  intro hact
  have hi := activeIndices10 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint10_02.conditions
  · exact EndpointAnalyticJoint10_03.conditions
  · exact EndpointAnalyticJoint10_04.conditions
  · exact EndpointAnalyticJoint10_05.conditions
  · exact EndpointAnalyticJoint10_06.conditions
  · exact EndpointAnalyticJoint10_07.conditions
  · exact EndpointAnalyticJoint10_08.conditions
  · exact EndpointAnalyticJoint10_09.conditions
  · exact EndpointAnalyticJoint10_10.conditions
  · exact EndpointAnalyticJoint10_11.conditions
  · exact EndpointAnalyticJoint10_12.conditions
  · exact EndpointAnalyticJoint10_13.conditions
  · exact EndpointAnalyticJoint10_14.conditions
  · exact EndpointAnalyticJoint10_15.conditions

private theorem activeIndices11 : ∀ai : Fin 42, endpointMeanActive 11 ai → ai∈
    ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow11 (ai : Fin 42) : endpointMeanActive 11 ai →
    EndpointJointNumericalConditions 11 ai := by
  intro hact
  have hi := activeIndices11 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint11_02.conditions
  · exact EndpointAnalyticJoint11_03.conditions
  · exact EndpointAnalyticJoint11_04.conditions
  · exact EndpointAnalyticJoint11_05.conditions
  · exact EndpointAnalyticJoint11_06.conditions
  · exact EndpointAnalyticJoint11_07.conditions
  · exact EndpointAnalyticJoint11_08.conditions
  · exact EndpointAnalyticJoint11_09.conditions
  · exact EndpointAnalyticJoint11_10.conditions
  · exact EndpointAnalyticJoint11_11.conditions
  · exact EndpointAnalyticJoint11_12.conditions
  · exact EndpointAnalyticJoint11_13.conditions
  · exact EndpointAnalyticJoint11_14.conditions
  · exact EndpointAnalyticJoint11_15.conditions
  · exact EndpointAnalyticJoint11_16.conditions

end SingularValueBounds.KL.Certificates
