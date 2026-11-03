import SingularValueBounds.KL.Certificates.EndpointAnalyticLogs
import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SingularValueBounds.KL.Certificates

namespace EndpointAnalyticJoint48_24
private noncomputable def weights : IntegerLookupTree := (.branch 2340 (.leaf (83837387600000:ℤ)) (.leaf (7452380000000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 121 (.leaf (2394014518554078:ℤ)) (.leaf (3335150618453691:ℤ))), (.branch 121 (.leaf (2408598530273440:ℤ)) (.leaf (3370746307116628:ℤ))), (.branch 121 (.leaf (2450265545563379:ℤ)) (.leaf (3585101691509506:ℤ))), (.branch 121 (.leaf (2466206290125039:ℤ)) (.leaf (3628005043204447:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 24) 8000 (endpointMeanRuns 48 24) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 48 24, EndpointRunConditions (endpointMeanCutoff 48 24) (endpointMeanBox 48 24).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 24, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 48 24 h) (endpointMeanCornerA 48 24 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 24, endpointJoint24Q (endpointMeanCornerK 48 24 h) (endpointMeanCornerA 48 24 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 48 24, endpointRunWeightQ (endpointMeanCutoff 48 24) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 48 24) = (355048453/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 48 24 h = (logRoundedQ ((endpointMeanCutoff 48 24:ℚ)/200)).2+(355048453/1000000000000000:ℚ)+((endpointMeanRuns 48 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 48 24).map (fun r => endpointRunWeightQ (endpointMeanCutoff 48 24) r*endpointJoint24Q (endpointMeanCornerK 48 24 h) (endpointMeanCornerA 48 24 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 48 24).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 48 24 h≤endpointMeanCorner 48 24 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 48 24 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint48_24

namespace EndpointAnalyticJoint48_25
private noncomputable def weights : IntegerLookupTree := (.branch 2340 (.leaf (84861920600000:ℤ)) (.leaf (7426871100000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 120 (.leaf (2408598530273440:ℤ)) (.leaf (3271958846603218:ℤ))), (.branch 120 (.leaf (2442462759328908:ℤ)) (.leaf (3349477604982617:ℤ))), (.branch 120 (.leaf (2466206290125039:ℤ)) (.leaf (3498435380585617:ℤ))), (.branch 120 (.leaf (2503246018778944:ℤ)) (.leaf (3590920110333730:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 25) 8000 (endpointMeanRuns 48 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 48 25, EndpointRunConditions (endpointMeanCutoff 48 25) (endpointMeanBox 48 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 48 25 h) (endpointMeanCornerA 48 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 25, endpointJoint24Q (endpointMeanCornerK 48 25 h) (endpointMeanCornerA 48 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 48 25, endpointRunWeightQ (endpointMeanCutoff 48 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 48 25) = (354282829/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 48 25 h = (logRoundedQ ((endpointMeanCutoff 48 25:ℚ)/200)).2+(354282829/1000000000000000:ℚ)+((endpointMeanRuns 48 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 48 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 48 25) r*endpointJoint24Q (endpointMeanCornerK 48 25 h) (endpointMeanCornerA 48 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 48 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 48 25 h≤endpointMeanCorner 48 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 48 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint48_25

namespace EndpointAnalyticJoint48_26
private noncomputable def weights : IntegerLookupTree := (.branch 2340 (.leaf (82151192800000:ℤ)) (.leaf (7390721600000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 120 (.leaf (2442462759328908:ℤ)) (.leaf (3349477604982617:ℤ))), (.branch 120 (.leaf (2476803110077182:ℤ)) (.leaf (3428832926161976:ℤ))), (.branch 120 (.leaf (2503246018778944:ℤ)) (.leaf (3590920110333730:ℤ))), (.branch 120 (.leaf (2540842043759013:ℤ)) (.leaf (3685849768830292:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 26) 8000 (endpointMeanRuns 48 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 48 26, EndpointRunConditions (endpointMeanCutoff 48 26) (endpointMeanBox 48 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 48 26 h) (endpointMeanCornerA 48 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 26, endpointJoint24Q (endpointMeanCornerK 48 26 h) (endpointMeanCornerA 48 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 48 26, endpointRunWeightQ (endpointMeanCutoff 48 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 48 26) = (353197839/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 48 26 h = (logRoundedQ ((endpointMeanCutoff 48 26:ℚ)/200)).2+(353197839/1000000000000000:ℚ)+((endpointMeanRuns 48 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 48 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 48 26) r*endpointJoint24Q (endpointMeanCornerK 48 26 h) (endpointMeanCornerA 48 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 48 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 48 26 h≤endpointMeanCorner 48 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 48 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint48_26

namespace EndpointAnalyticJoint48_27
private noncomputable def weights : IntegerLookupTree := (.leaf (138767593800000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2476803110077182:ℤ)), (.leaf (2511626276657553:ℤ)), (.leaf (2540842043759013:ℤ)), (.leaf (2579002720029325:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 27) 8000 (endpointMeanRuns 48 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 48 27, EndpointRunConditions (endpointMeanCutoff 48 27) (endpointMeanBox 48 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 48 27 h) (endpointMeanCornerA 48 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 27, endpointJoint24Q (endpointMeanCornerK 48 27 h) (endpointMeanCornerA 48 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 48 27, endpointRunWeightQ (endpointMeanCutoff 48 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 48 27) = (17606149/50000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 48 27 h = (logRoundedQ ((endpointMeanCutoff 48 27:ℚ)/200)).2+(17606149/50000000000000:ℚ)+((endpointMeanRuns 48 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 48 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 48 27) r*endpointJoint24Q (endpointMeanCornerK 48 27 h) (endpointMeanCornerA 48 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 48 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 48 27 h≤endpointMeanCorner 48 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 48 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint48_27

namespace EndpointAnalyticJoint48_28
private noncomputable def weights : IntegerLookupTree := (.leaf (134921554100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2511626276657553:ℤ)), (.leaf (2546939047327066:ℤ)), (.leaf (2579002720029325:ℤ)), (.leaf (2617736528036409:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 28) 8000 (endpointMeanRuns 48 28) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 48 28, EndpointRunConditions (endpointMeanCutoff 48 28) (endpointMeanBox 48 28).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 28, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 48 28 h) (endpointMeanCornerA 48 28 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 28, endpointJoint24Q (endpointMeanCornerK 48 28 h) (endpointMeanCornerA 48 28 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 48 28, endpointRunWeightQ (endpointMeanCutoff 48 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 48 28) = (21941129/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 48 28 h = (logRoundedQ ((endpointMeanCutoff 48 28:ℚ)/200)).2+(21941129/62500000000000:ℚ)+((endpointMeanRuns 48 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 48 28).map (fun r => endpointRunWeightQ (endpointMeanCutoff 48 28) r*endpointJoint24Q (endpointMeanCornerK 48 28 h) (endpointMeanCornerA 48 28 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 48 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 48 28 h≤endpointMeanCorner 48 28 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 48 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint48_28

namespace EndpointAnalyticJoint48_29
private noncomputable def weights : IntegerLookupTree := (.leaf (131923719100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2546939047327066:ℤ)), (.leaf (2568364579299543:ℤ)), (.leaf (2617736528036409:ℤ)), (.leaf (2641255491569198:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 29) 8000 (endpointMeanRuns 48 29) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 48 29, EndpointRunConditions (endpointMeanCutoff 48 29) (endpointMeanBox 48 29).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 29, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 48 29 h) (endpointMeanCornerA 48 29 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 29, endpointJoint24Q (endpointMeanCornerK 48 29 h) (endpointMeanCornerA 48 29 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 48 29, endpointRunWeightQ (endpointMeanCutoff 48 29) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 48 29) = (350213167/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 48 29 h = (logRoundedQ ((endpointMeanCutoff 48 29:ℚ)/200)).2+(350213167/1000000000000000:ℚ)+((endpointMeanRuns 48 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 48 29).map (fun r => endpointRunWeightQ (endpointMeanCutoff 48 29) r*endpointJoint24Q (endpointMeanCornerK 48 29 h) (endpointMeanCornerA 48 29 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 48 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 48 29 h≤endpointMeanCorner 48 29 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 48 29 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint48_29

namespace EndpointAnalyticJoint48_30
private noncomputable def weights : IntegerLookupTree := (.leaf (130450556200000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2568364579299543:ℤ)), (.leaf (2582748305783772:ℤ)), (.leaf (2641255491569198:ℤ)), (.leaf (2657052075593857:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 30) 8000 (endpointMeanRuns 48 30) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 48 30, EndpointRunConditions (endpointMeanCutoff 48 30) (endpointMeanBox 48 30).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 30, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 48 30 h) (endpointMeanCornerA 48 30 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 30, endpointJoint24Q (endpointMeanCornerK 48 30 h) (endpointMeanCornerA 48 30 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 48 30, endpointRunWeightQ (endpointMeanCutoff 48 30) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 48 30) = (349793033/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 48 30 h = (logRoundedQ ((endpointMeanCutoff 48 30:ℚ)/200)).2+(349793033/1000000000000000:ℚ)+((endpointMeanRuns 48 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 48 30).map (fun r => endpointRunWeightQ (endpointMeanCutoff 48 30) r*endpointJoint24Q (endpointMeanCornerK 48 30 h) (endpointMeanCornerA 48 30 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 48 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 48 30 h≤endpointMeanCorner 48 30 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 48 30 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint48_30

namespace EndpointAnalyticJoint48_31
private noncomputable def weights : IntegerLookupTree := (.leaf (127913054100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2582748305783772:ℤ)), (.leaf (2619061032508619:ℤ)), (.leaf (2657052075593857:ℤ)), (.leaf (2696958099795221:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 31) 8000 (endpointMeanRuns 48 31) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 48 31, EndpointRunConditions (endpointMeanCutoff 48 31) (endpointMeanBox 48 31).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 31, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 48 31 h) (endpointMeanCornerA 48 31 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 31, endpointJoint24Q (endpointMeanCornerK 48 31 h) (endpointMeanCornerA 48 31 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 48 31, endpointRunWeightQ (endpointMeanCutoff 48 31) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 48 31) = (87265367/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 48 31 h = (logRoundedQ ((endpointMeanCutoff 48 31:ℚ)/200)).2+(87265367/250000000000000:ℚ)+((endpointMeanRuns 48 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 48 31).map (fun r => endpointRunWeightQ (endpointMeanCutoff 48 31) r*endpointJoint24Q (endpointMeanCornerK 48 31 h) (endpointMeanCornerA 48 31 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 48 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 48 31 h≤endpointMeanCorner 48 31 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 48 31 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint48_31

namespace EndpointAnalyticJoint48_32
private noncomputable def weights : IntegerLookupTree := (.leaf (124375676500000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2619061032508619:ℤ)), (.leaf (2655884306126184:ℤ)), (.leaf (2696958099795221:ℤ)), (.leaf (2737463468955688:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 32) 8000 (endpointMeanRuns 48 32) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 48 32, EndpointRunConditions (endpointMeanCutoff 48 32) (endpointMeanBox 48 32).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 32, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 48 32 h) (endpointMeanCornerA 48 32 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 32, endpointJoint24Q (endpointMeanCornerK 48 32 h) (endpointMeanCornerA 48 32 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 48 32, endpointRunWeightQ (endpointMeanCutoff 48 32) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 48 32) = (174012187/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 48 32 h = (logRoundedQ ((endpointMeanCutoff 48 32:ℚ)/200)).2+(174012187/500000000000000:ℚ)+((endpointMeanRuns 48 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 48 32).map (fun r => endpointRunWeightQ (endpointMeanCutoff 48 32) r*endpointJoint24Q (endpointMeanCornerK 48 32 h) (endpointMeanCornerA 48 32 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 48 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 48 32 h≤endpointMeanCorner 48 32 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 48 32 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint48_32

namespace EndpointAnalyticJoint48_33
private noncomputable def weights : IntegerLookupTree := (.leaf (120938638900000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2655884306126184:ℤ)), (.leaf (2693225304784549:ℤ)), (.leaf (2737463468955688:ℤ)), (.leaf (2778577184582842:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 33) 8000 (endpointMeanRuns 48 33) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 48 33, EndpointRunConditions (endpointMeanCutoff 48 33) (endpointMeanBox 48 33).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 33, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 48 33 h) (endpointMeanCornerA 48 33 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 33, endpointJoint24Q (endpointMeanCornerK 48 33 h) (endpointMeanCornerA 48 33 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 48 33, endpointRunWeightQ (endpointMeanCutoff 48 33) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 48 33) = (346996541/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 48 33 h = (logRoundedQ ((endpointMeanCutoff 48 33:ℚ)/200)).2+(346996541/1000000000000000:ℚ)+((endpointMeanRuns 48 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 48 33).map (fun r => endpointRunWeightQ (endpointMeanCutoff 48 33) r*endpointJoint24Q (endpointMeanCornerK 48 33 h) (endpointMeanCornerA 48 33 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 48 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 48 33 h≤endpointMeanCorner 48 33 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 48 33 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint48_33

namespace EndpointAnalyticJoint48_34
private noncomputable def weights : IntegerLookupTree := (.leaf (118590823300000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2693225304784549:ℤ)), (.leaf (2705788609523035:ℤ)), (.leaf (2778577184582842:ℤ)), (.leaf (2792418519811780:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 34) 8000 (endpointMeanRuns 48 34) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 48 34, EndpointRunConditions (endpointMeanCutoff 48 34) (endpointMeanBox 48 34).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 34, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 48 34 h) (endpointMeanCornerA 48 34 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 34, endpointJoint24Q (endpointMeanCornerK 48 34 h) (endpointMeanCornerA 48 34 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 48 34, endpointRunWeightQ (endpointMeanCutoff 48 34) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 48 34) = (346282479/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 48 34 h = (logRoundedQ ((endpointMeanCutoff 48 34:ℚ)/200)).2+(346282479/1000000000000000:ℚ)+((endpointMeanRuns 48 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 48 34).map (fun r => endpointRunWeightQ (endpointMeanCutoff 48 34) r*endpointJoint24Q (endpointMeanCornerK 48 34 h) (endpointMeanCornerA 48 34 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 48 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 48 34 h≤endpointMeanCorner 48 34 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 48 34 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint48_34

namespace EndpointAnalyticJoint48_35
private noncomputable def weights : IntegerLookupTree := (.leaf (117270254400000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2705788609523035:ℤ)), (.leaf (2731091307554576:ℤ)), (.leaf (2792418519811780:ℤ)), (.leaf (2820308383377108:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 35) 8000 (endpointMeanRuns 48 35) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 48 35, EndpointRunConditions (endpointMeanCutoff 48 35) (endpointMeanBox 48 35).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 35, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 48 35 h) (endpointMeanCornerA 48 35 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 35, endpointJoint24Q (endpointMeanCornerK 48 35 h) (endpointMeanCornerA 48 35 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 48 35, endpointRunWeightQ (endpointMeanCutoff 48 35) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 48 35) = (345876423/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 48 35 h = (logRoundedQ ((endpointMeanCutoff 48 35:ℚ)/200)).2+(345876423/1000000000000000:ℚ)+((endpointMeanRuns 48 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 48 35).map (fun r => endpointRunWeightQ (endpointMeanCutoff 48 35) r*endpointJoint24Q (endpointMeanCornerK 48 35 h) (endpointMeanCornerA 48 35 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 48 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 48 35 h≤endpointMeanCorner 48 35 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 48 35 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint48_35

namespace EndpointAnalyticJoint48_36
private noncomputable def weights : IntegerLookupTree := (.leaf (114353817800000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2731091307554576:ℤ)), (.leaf (2769489695848837:ℤ)), (.leaf (2820308383377108:ℤ)), (.leaf (2862666339262190:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 48 36) 8000 (endpointMeanRuns 48 36) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 48 36, EndpointRunConditions (endpointMeanCutoff 48 36) (endpointMeanBox 48 36).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 36, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 48 36 h) (endpointMeanCornerA 48 36 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 48 36, endpointJoint24Q (endpointMeanCornerK 48 36 h) (endpointMeanCornerA 48 36 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 48 36, endpointRunWeightQ (endpointMeanCutoff 48 36) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 48 36) = (172484001/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 48 36 h = (logRoundedQ ((endpointMeanCutoff 48 36:ℚ)/200)).2+(172484001/500000000000000:ℚ)+((endpointMeanRuns 48 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 48 36).map (fun r => endpointRunWeightQ (endpointMeanCutoff 48 36) r*endpointJoint24Q (endpointMeanCornerK 48 36 h) (endpointMeanCornerA 48 36 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 48 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 48 36 h≤endpointMeanCorner 48 36 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 48 36 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint48_36

namespace EndpointAnalyticJoint49_25
private noncomputable def weights : IntegerLookupTree := (.branch 2526 (.leaf (84795756400000:ℤ)) (.leaf (4635077400000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 118 (.leaf (2490767453292188:ℤ)) (.leaf (3327368626417704:ℤ))), (.branch 118 (.leaf (2503246018778944:ℤ)) (.leaf (3354082084280794:ℤ))), (.branch 118 (.leaf (2561520431938664:ℤ)) (.leaf (3585038755325889:ℤ))), (.branch 118 (.leaf (2575295514625816:ℤ)) (.leaf (3617343429149870:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 49 25) 8000 (endpointMeanRuns 49 25) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 49 25, EndpointRunConditions (endpointMeanCutoff 49 25) (endpointMeanBox 49 25).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 25, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 49 25 h) (endpointMeanCornerA 49 25 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 25, endpointJoint24Q (endpointMeanCornerK 49 25 h) (endpointMeanCornerA 49 25 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 49 25, endpointRunWeightQ (endpointMeanCutoff 49 25) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 49 25) = (70275301/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 49 25 h = (logRoundedQ ((endpointMeanCutoff 49 25:ℚ)/200)).2+(70275301/200000000000000:ℚ)+((endpointMeanRuns 49 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 49 25).map (fun r => endpointRunWeightQ (endpointMeanCutoff 49 25) r*endpointJoint24Q (endpointMeanCornerK 49 25 h) (endpointMeanCornerA 49 25 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 49 25).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 49 25 h≤endpointMeanCorner 49 25 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 49 25 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint49_25

namespace EndpointAnalyticJoint49_26
private noncomputable def weights : IntegerLookupTree := (.branch 2526 (.leaf (86278423100000:ℤ)) (.leaf (4622133200000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 117 (.leaf (2503246018778944:ℤ)) (.leaf (3251155660724803:ℤ))), (.branch 117 (.leaf (2540842043759013:ℤ)) (.leaf (3326288372648796:ℤ))), (.branch 117 (.leaf (2575295514625816:ℤ)) (.leaf (3481411802813614:ℤ))), (.branch 117 (.leaf (2616828051743351:ℤ)) (.leaf (3571252172258023:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 49 26) 8000 (endpointMeanRuns 49 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 49 26, EndpointRunConditions (endpointMeanCutoff 49 26) (endpointMeanBox 49 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 49 26 h) (endpointMeanCornerA 49 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 26, endpointJoint24Q (endpointMeanCornerK 49 26 h) (endpointMeanCornerA 49 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 49 26, endpointRunWeightQ (endpointMeanCutoff 49 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 49 26) = (701481/2000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 49 26 h = (logRoundedQ ((endpointMeanCutoff 49 26:ℚ)/200)).2+(701481/2000000000000:ℚ)+((endpointMeanRuns 49 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 49 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 49 26) r*endpointJoint24Q (endpointMeanCornerK 49 26 h) (endpointMeanCornerA 49 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 49 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 49 26 h≤endpointMeanCorner 49 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 49 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint49_26

namespace EndpointAnalyticJoint49_27
private noncomputable def weights : IntegerLookupTree := (.branch 3120 (.leaf (85282511200000:ℤ)) (.leaf (1044704300000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 117 (.leaf (2540842043759013:ℤ)) (.leaf (3326288372648796:ℤ))), (.branch 117 (.leaf (2579002720029325:ℤ)) (.leaf (3403157366987451:ℤ))), (.branch 117 (.leaf (2616828051743351:ℤ)) (.leaf (3571252172258023:ℤ))), (.branch 117 (.leaf (2659030396123633:ℤ)) (.leaf (3663410937927607:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 49 27) 8000 (endpointMeanRuns 49 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 49 27, EndpointRunConditions (endpointMeanCutoff 49 27) (endpointMeanBox 49 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 49 27 h) (endpointMeanCornerA 49 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 27, endpointJoint24Q (endpointMeanCornerK 49 27 h) (endpointMeanCornerA 49 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 49 27, endpointRunWeightQ (endpointMeanCutoff 49 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 49 27) = (349688239/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 49 27 h = (logRoundedQ ((endpointMeanCutoff 49 27:ℚ)/200)).2+(349688239/1000000000000000:ℚ)+((endpointMeanRuns 49 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 49 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 49 27) r*endpointJoint24Q (endpointMeanCornerK 49 27 h) (endpointMeanCornerA 49 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 49 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 49 27 h≤endpointMeanCorner 49 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 49 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint49_27

namespace EndpointAnalyticJoint49_28
private noncomputable def weights : IntegerLookupTree := (.leaf (126485868600000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2579002720029325:ℤ)), (.leaf (2617736528036409:ℤ)), (.leaf (2659030396123633:ℤ)), (.leaf (2701913349942515:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 49 28) 8000 (endpointMeanRuns 49 28) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 49 28, EndpointRunConditions (endpointMeanCutoff 49 28) (endpointMeanBox 49 28).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 28, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 49 28 h) (endpointMeanCornerA 49 28 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 28, endpointJoint24Q (endpointMeanCornerK 49 28 h) (endpointMeanCornerA 49 28 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 49 28, endpointRunWeightQ (endpointMeanCutoff 49 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 49 28) = (348645509/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 49 28 h = (logRoundedQ ((endpointMeanCutoff 49 28:ℚ)/200)).2+(348645509/1000000000000000:ℚ)+((endpointMeanRuns 49 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 49 28).map (fun r => endpointRunWeightQ (endpointMeanCutoff 49 28) r*endpointJoint24Q (endpointMeanCornerK 49 28 h) (endpointMeanCornerA 49 28 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 49 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 49 28 h≤endpointMeanCorner 49 28 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 49 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint49_28

namespace EndpointAnalyticJoint49_29
private noncomputable def weights : IntegerLookupTree := (.leaf (123680338100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2617736528036409:ℤ)), (.leaf (2641255491569198:ℤ)), (.leaf (2701913349942515:ℤ)), (.leaf (2727974373609836:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 49 29) 8000 (endpointMeanRuns 49 29) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 49 29, EndpointRunConditions (endpointMeanCutoff 49 29) (endpointMeanBox 49 29).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 29, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 49 29 h) (endpointMeanCornerA 49 29 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 29, endpointJoint24Q (endpointMeanCornerK 49 29 h) (endpointMeanCornerA 49 29 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 49 29, endpointRunWeightQ (endpointMeanCutoff 49 29) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 49 29) = (43477259/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 49 29 h = (logRoundedQ ((endpointMeanCutoff 49 29:ℚ)/200)).2+(43477259/125000000000000:ℚ)+((endpointMeanRuns 49 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 49 29).map (fun r => endpointRunWeightQ (endpointMeanCutoff 49 29) r*endpointJoint24Q (endpointMeanCornerK 49 29 h) (endpointMeanCornerA 49 29 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 49 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 49 29 h≤endpointMeanCorner 49 29 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 49 29 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint49_29

namespace EndpointAnalyticJoint49_30
private noncomputable def weights : IntegerLookupTree := (.leaf (121959392700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2641255491569198:ℤ)), (.leaf (2657052075593857:ℤ)), (.leaf (2727974373609836:ℤ)), (.leaf (2745487889585649:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 49 30) 8000 (endpointMeanRuns 49 30) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 49 30, EndpointRunConditions (endpointMeanCutoff 49 30) (endpointMeanBox 49 30).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 30, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 49 30 h) (endpointMeanCornerA 49 30 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 30, endpointJoint24Q (endpointMeanCornerK 49 30 h) (endpointMeanCornerA 49 30 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 49 30, endpointRunWeightQ (endpointMeanCutoff 49 30) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 49 30) = (43412991/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 49 30 h = (logRoundedQ ((endpointMeanCutoff 49 30:ℚ)/200)).2+(43412991/125000000000000:ℚ)+((endpointMeanRuns 49 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 49 30).map (fun r => endpointRunWeightQ (endpointMeanCutoff 49 30) r*endpointJoint24Q (endpointMeanCornerK 49 30 h) (endpointMeanCornerA 49 30 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 49 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 49 30 h≤endpointMeanCorner 49 30 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 49 30 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint49_30

namespace EndpointAnalyticJoint49_31
private noncomputable def weights : IntegerLookupTree := (.leaf (119591251700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2657052075593857:ℤ)), (.leaf (2696958099795221:ℤ)), (.leaf (2745487889585649:ℤ)), (.leaf (2789765168458060:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 49 31) 8000 (endpointMeanRuns 49 31) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 49 31, EndpointRunConditions (endpointMeanCutoff 49 31) (endpointMeanBox 49 31).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 31, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 49 31 h) (endpointMeanCornerA 49 31 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 31, endpointJoint24Q (endpointMeanCornerK 49 31 h) (endpointMeanCornerA 49 31 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 49 31, endpointRunWeightQ (endpointMeanCutoff 49 31) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 49 31) = (346587963/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 49 31 h = (logRoundedQ ((endpointMeanCutoff 49 31:ℚ)/200)).2+(346587963/1000000000000000:ℚ)+((endpointMeanRuns 49 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 49 31).map (fun r => endpointRunWeightQ (endpointMeanCutoff 49 31) r*endpointJoint24Q (endpointMeanCornerK 49 31 h) (endpointMeanCornerA 49 31 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 49 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 49 31 h≤endpointMeanCorner 49 31 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 49 31 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint49_31

namespace EndpointAnalyticJoint49_32
private noncomputable def weights : IntegerLookupTree := (.leaf (116289730100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2696958099795221:ℤ)), (.leaf (2737463468955688:ℤ)), (.leaf (2789765168458060:ℤ)), (.leaf (2834756519838967:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 49 32) 8000 (endpointMeanRuns 49 32) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 49 32, EndpointRunConditions (endpointMeanCutoff 49 32) (endpointMeanBox 49 32).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 32, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 49 32 h) (endpointMeanCornerA 49 32 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 32, endpointJoint24Q (endpointMeanCornerK 49 32 h) (endpointMeanCornerA 49 32 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 49 32, endpointRunWeightQ (endpointMeanCutoff 49 32) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 49 32) = (345572819/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 49 32 h = (logRoundedQ ((endpointMeanCutoff 49 32:ℚ)/200)).2+(345572819/1000000000000000:ℚ)+((endpointMeanRuns 49 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 49 32).map (fun r => endpointRunWeightQ (endpointMeanCutoff 49 32) r*endpointJoint24Q (endpointMeanCornerK 49 32 h) (endpointMeanCornerA 49 32 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 49 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 49 32 h≤endpointMeanCorner 49 32 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 49 32 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint49_32

namespace EndpointAnalyticJoint49_33
private noncomputable def weights : IntegerLookupTree := (.leaf (113081589500000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2737463468955688:ℤ)), (.leaf (2778577184582842:ℤ)), (.leaf (2834756519838967:ℤ)), (.leaf (2880473459782649:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 49 33) 8000 (endpointMeanRuns 49 33) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 49 33, EndpointRunConditions (endpointMeanCutoff 49 33) (endpointMeanBox 49 33).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 33, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 49 33 h) (endpointMeanCornerA 49 33 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 33, endpointJoint24Q (endpointMeanCornerK 49 33 h) (endpointMeanCornerA 49 33 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 49 33, endpointRunWeightQ (endpointMeanCutoff 49 33) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 49 33) = (86141637/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 49 33 h = (logRoundedQ ((endpointMeanCutoff 49 33:ℚ)/200)).2+(86141637/250000000000000:ℚ)+((endpointMeanRuns 49 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 49 33).map (fun r => endpointRunWeightQ (endpointMeanCutoff 49 33) r*endpointJoint24Q (endpointMeanCornerK 49 33 h) (endpointMeanCornerA 49 33 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 49 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 49 33 h≤endpointMeanCorner 49 33 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 49 33 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint49_33

namespace EndpointAnalyticJoint49_34
private noncomputable def weights : IntegerLookupTree := (.leaf (110889978900000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2778577184582842:ℤ)), (.leaf (2792418519811780:ℤ)), (.leaf (2880473459782649:ℤ)), (.leaf (2895875698788780:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 49 34) 8000 (endpointMeanRuns 49 34) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 49 34, EndpointRunConditions (endpointMeanCutoff 49 34) (endpointMeanBox 49 34).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 34, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 49 34 h) (endpointMeanCornerA 49 34 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 34, endpointJoint24Q (endpointMeanCornerK 49 34 h) (endpointMeanCornerA 49 34 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 49 34, endpointRunWeightQ (endpointMeanCutoff 49 34) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 49 34) = (85966839/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 49 34 h = (logRoundedQ ((endpointMeanCutoff 49 34:ℚ)/200)).2+(85966839/250000000000000:ℚ)+((endpointMeanRuns 49 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 49 34).map (fun r => endpointRunWeightQ (endpointMeanCutoff 49 34) r*endpointJoint24Q (endpointMeanCornerK 49 34 h) (endpointMeanCornerA 49 34 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 49 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 49 34 h≤endpointMeanCorner 49 34 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 49 34 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint49_34

namespace EndpointAnalyticJoint49_35
private noncomputable def weights : IntegerLookupTree := (.leaf (109351223700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2792418519811780:ℤ)), (.leaf (2820308383377108:ℤ)), (.leaf (2895875698788780:ℤ)), (.leaf (2926927690066150:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 49 35) 8000 (endpointMeanRuns 49 35) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 49 35, EndpointRunConditions (endpointMeanCutoff 49 35) (endpointMeanBox 49 35).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 35, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 49 35 h) (endpointMeanCornerA 49 35 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 35, endpointJoint24Q (endpointMeanCornerK 49 35 h) (endpointMeanCornerA 49 35 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 49 35, endpointRunWeightQ (endpointMeanCutoff 49 35) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 49 35) = (343370521/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 49 35 h = (logRoundedQ ((endpointMeanCutoff 49 35:ℚ)/200)).2+(343370521/1000000000000000:ℚ)+((endpointMeanRuns 49 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 49 35).map (fun r => endpointRunWeightQ (endpointMeanCutoff 49 35) r*endpointJoint24Q (endpointMeanCornerK 49 35 h) (endpointMeanCornerA 49 35 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 49 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 49 35 h≤endpointMeanCorner 49 35 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 49 35 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint49_35

namespace EndpointAnalyticJoint49_36
private noncomputable def weights : IntegerLookupTree := (.leaf (106934554000000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2820308383377108:ℤ)), (.leaf (2862666339262190:ℤ)), (.leaf (2926927690066150:ℤ)), (.leaf (2974131101184460:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 49 36) 8000 (endpointMeanRuns 49 36) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 49 36, EndpointRunConditions (endpointMeanCutoff 49 36) (endpointMeanBox 49 36).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 36, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 49 36 h) (endpointMeanCornerA 49 36 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 36, endpointJoint24Q (endpointMeanCornerK 49 36 h) (endpointMeanCornerA 49 36 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 49 36, endpointRunWeightQ (endpointMeanCutoff 49 36) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 49 36) = (171290009/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 49 36 h = (logRoundedQ ((endpointMeanCutoff 49 36:ℚ)/200)).2+(171290009/500000000000000:ℚ)+((endpointMeanRuns 49 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 49 36).map (fun r => endpointRunWeightQ (endpointMeanCutoff 49 36) r*endpointJoint24Q (endpointMeanCornerK 49 36 h) (endpointMeanCornerA 49 36 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 49 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 49 36 h≤endpointMeanCorner 49 36 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 49 36 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint49_36

namespace EndpointAnalyticJoint49_37
private noncomputable def weights : IntegerLookupTree := (.leaf (103990422400000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2862666339262190:ℤ)), (.leaf (2905660465445998:ℤ)), (.leaf (2974131101184460:ℤ)), (.leaf (3022095775394014:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 49 37) 8000 (endpointMeanRuns 49 37) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 49 37, EndpointRunConditions (endpointMeanCutoff 49 37) (endpointMeanBox 49 37).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 37, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 49 37 h) (endpointMeanCornerA 49 37 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 49 37, endpointJoint24Q (endpointMeanCornerK 49 37 h) (endpointMeanCornerA 49 37 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 49 37, endpointRunWeightQ (endpointMeanCutoff 49 37) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 49 37) = (341599461/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 49 37 h = (logRoundedQ ((endpointMeanCutoff 49 37:ℚ)/200)).2+(341599461/1000000000000000:ℚ)+((endpointMeanRuns 49 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 49 37).map (fun r => endpointRunWeightQ (endpointMeanCutoff 49 37) r*endpointJoint24Q (endpointMeanCornerK 49 37 h) (endpointMeanCornerA 49 37 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 49 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 49 37 h≤endpointMeanCorner 49 37 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 49 37 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint49_37

namespace EndpointAnalyticJoint50_26
private noncomputable def weights : IntegerLookupTree := (.branch 3076 (.leaf (86933561700000:ℤ)) (.leaf (1158063600000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 115 (.leaf (2608337893414071:ℤ)) (.leaf (3309689382235690:ℤ))), (.branch 115 (.leaf (2616828051743351:ℤ)) (.leaf (3325327306997917:ℤ))), (.branch 115 (.leaf (2699485338097990:ℤ)) (.leaf (3571367768232059:ℤ))), (.branch 115 (.leaf (2708977408812987:ℤ)) (.leaf (3590312419470704:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 50 26) 8000 (endpointMeanRuns 50 26) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 50 26, EndpointRunConditions (endpointMeanCutoff 50 26) (endpointMeanBox 50 26).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 26, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 50 26 h) (endpointMeanCornerA 50 26 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 26, endpointJoint24Q (endpointMeanCornerK 50 26 h) (endpointMeanCornerA 50 26 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 50 26, endpointRunWeightQ (endpointMeanCutoff 50 26) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 50 26) = (43477259/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 50 26 h = (logRoundedQ ((endpointMeanCutoff 50 26:ℚ)/200)).2+(43477259/125000000000000:ℚ)+((endpointMeanRuns 50 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 50 26).map (fun r => endpointRunWeightQ (endpointMeanCutoff 50 26) r*endpointJoint24Q (endpointMeanCornerK 50 26 h) (endpointMeanCornerA 50 26 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 50 26).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 50 26 h≤endpointMeanCorner 50 26 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 50 26 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint50_26

namespace EndpointAnalyticJoint50_27
private noncomputable def weights : IntegerLookupTree := (.branch 3076 (.leaf (88664144300000:ℤ)) (.leaf (1155141400000:ℤ)))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.branch 114 (.leaf (2616828051743351:ℤ)) (.leaf (3219247634651309:ℤ))), (.branch 114 (.leaf (2659030396123633:ℤ)) (.leaf (3291483362334105:ℤ))), (.branch 114 (.leaf (2708977408812987:ℤ)) (.leaf (3449639691809715:ℤ))), (.branch 114 (.leaf (2756196472053774:ℤ)) (.leaf (3536086196574674:ℤ)))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 50 27) 8000 (endpointMeanRuns 50 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 50 27, EndpointRunConditions (endpointMeanCutoff 50 27) (endpointMeanBox 50 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 50 27 h) (endpointMeanCornerA 50 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 27, endpointJoint24Q (endpointMeanCornerK 50 27 h) (endpointMeanCornerA 50 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 50 27, endpointRunWeightQ (endpointMeanCutoff 50 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 50 27) = (2777611/8000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 50 27 h = (logRoundedQ ((endpointMeanCutoff 50 27:ℚ)/200)).2+(2777611/8000000000000:ℚ)+((endpointMeanRuns 50 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 50 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 50 27) r*endpointJoint24Q (endpointMeanCornerK 50 27 h) (endpointMeanCornerA 50 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 50 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 50 27 h≤endpointMeanCorner 50 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 50 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint50_27

namespace EndpointAnalyticJoint50_28
private noncomputable def weights : IntegerLookupTree := (.leaf (118259258000000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2659030396123633:ℤ)), (.leaf (2701913349942515:ℤ)), (.leaf (2756196472053774:ℤ)), (.leaf (2804238591229282:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 50 28) 8000 (endpointMeanRuns 50 28) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 50 28, EndpointRunConditions (endpointMeanCutoff 50 28) (endpointMeanBox 50 28).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 28, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 50 28 h) (endpointMeanCornerA 50 28 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 28, endpointJoint24Q (endpointMeanCornerK 50 28 h) (endpointMeanCornerA 50 28 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 50 28, endpointRunWeightQ (endpointMeanCutoff 50 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 50 28) = (346180831/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 50 28 h = (logRoundedQ ((endpointMeanCutoff 50 28:ℚ)/200)).2+(346180831/1000000000000000:ℚ)+((endpointMeanRuns 50 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 50 28).map (fun r => endpointRunWeightQ (endpointMeanCutoff 50 28) r*endpointJoint24Q (endpointMeanCornerK 50 28 h) (endpointMeanCornerA 50 28 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 50 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 50 28 h≤endpointMeanCorner 50 28 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 50 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint50_28

namespace EndpointAnalyticJoint50_29
private noncomputable def weights : IntegerLookupTree := (.leaf (115640720700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2701913349942515:ℤ)), (.leaf (2727974373609836:ℤ)), (.leaf (2804238591229282:ℤ)), (.leaf (2833464887311356:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 50 29) 8000 (endpointMeanRuns 50 29) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 50 29, EndpointRunConditions (endpointMeanCutoff 50 29) (endpointMeanBox 50 29).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 29, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 50 29 h) (endpointMeanCornerA 50 29 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 29, endpointJoint24Q (endpointMeanCornerK 50 29 h) (endpointMeanCornerA 50 29 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 50 29, endpointRunWeightQ (endpointMeanCutoff 50 29) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 50 29) = (17268543/50000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 50 29 h = (logRoundedQ ((endpointMeanCutoff 50 29:ℚ)/200)).2+(17268543/50000000000000:ℚ)+((endpointMeanRuns 50 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 50 29).map (fun r => endpointRunWeightQ (endpointMeanCutoff 50 29) r*endpointJoint24Q (endpointMeanCornerK 50 29 h) (endpointMeanCornerA 50 29 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 50 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 50 29 h≤endpointMeanCorner 50 29 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 50 29 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint50_29

namespace EndpointAnalyticJoint50_30
private noncomputable def weights : IntegerLookupTree := (.leaf (114034391800000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2727974373609836:ℤ)), (.leaf (2745487889585649:ℤ)), (.leaf (2833464887311356:ℤ)), (.leaf (2853118112686622:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 50 30) 8000 (endpointMeanRuns 50 30) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 50 30, EndpointRunConditions (endpointMeanCutoff 50 30) (endpointMeanBox 50 30).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 30, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 50 30 h) (endpointMeanCornerA 50 30 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 30, endpointJoint24Q (endpointMeanCornerK 50 30 h) (endpointMeanCornerA 50 30 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 50 30, endpointRunWeightQ (endpointMeanCutoff 50 30) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 50 30) = (344867507/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 50 30 h = (logRoundedQ ((endpointMeanCutoff 50 30:ℚ)/200)).2+(344867507/1000000000000000:ℚ)+((endpointMeanRuns 50 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 50 30).map (fun r => endpointRunWeightQ (endpointMeanCutoff 50 30) r*endpointJoint24Q (endpointMeanCornerK 50 30 h) (endpointMeanCornerA 50 30 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 50 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 50 30 h≤endpointMeanCorner 50 30 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 50 30 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint50_30

namespace EndpointAnalyticJoint50_31
private noncomputable def weights : IntegerLookupTree := (.leaf (111823862000000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2745487889585649:ℤ)), (.leaf (2789765168458060:ℤ)), (.leaf (2853118112686622:ℤ)), (.leaf (2902849632838139:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 50 31) 8000 (endpointMeanRuns 50 31) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 50 31, EndpointRunConditions (endpointMeanCutoff 50 31) (endpointMeanBox 50 31).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 31, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 50 31 h) (endpointMeanCornerA 50 31 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 31, endpointJoint24Q (endpointMeanCornerK 50 31 h) (endpointMeanCornerA 50 31 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 50 31, endpointRunWeightQ (endpointMeanCutoff 50 31) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 50 31) = (34416649/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 50 31 h = (logRoundedQ ((endpointMeanCutoff 50 31:ℚ)/200)).2+(34416649/100000000000000:ℚ)+((endpointMeanRuns 50 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 50 31).map (fun r => endpointRunWeightQ (endpointMeanCutoff 50 31) r*endpointJoint24Q (endpointMeanCornerK 50 31 h) (endpointMeanCornerA 50 31 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 50 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 50 31 h≤endpointMeanCorner 50 31 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 50 31 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint50_31

namespace EndpointAnalyticJoint50_32
private noncomputable def weights : IntegerLookupTree := (.leaf (108741861200000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2789765168458060:ℤ)), (.leaf (2834756519838967:ℤ)), (.leaf (2902849632838139:ℤ)), (.leaf (2953448002520204:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 50 32) 8000 (endpointMeanRuns 50 32) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 50 32, EndpointRunConditions (endpointMeanCutoff 50 32) (endpointMeanBox 50 32).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 32, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 50 32 h) (endpointMeanCornerA 50 32 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 32, endpointJoint24Q (endpointMeanCornerK 50 32 h) (endpointMeanCornerA 50 32 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 50 32, endpointRunWeightQ (endpointMeanCutoff 50 32) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 50 32) = (171586193/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 50 32 h = (logRoundedQ ((endpointMeanCutoff 50 32:ℚ)/200)).2+(171586193/500000000000000:ℚ)+((endpointMeanRuns 50 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 50 32).map (fun r => endpointRunWeightQ (endpointMeanCutoff 50 32) r*endpointJoint24Q (endpointMeanCornerK 50 32 h) (endpointMeanCornerA 50 32 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 50 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 50 32 h≤endpointMeanCorner 50 32 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 50 32 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint50_32

namespace EndpointAnalyticJoint50_33
private noncomputable def weights : IntegerLookupTree := (.leaf (105746795100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2834756519838967:ℤ)), (.leaf (2880473459782649:ℤ)), (.leaf (2953448002520204:ℤ)), (.leaf (3004928331427966:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 50 33) 8000 (endpointMeanRuns 50 33) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 50 33, EndpointRunConditions (endpointMeanCutoff 50 33) (endpointMeanBox 50 33).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 33, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 50 33 h) (endpointMeanCornerA 50 33 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 33, endpointJoint24Q (endpointMeanCornerK 50 33 h) (endpointMeanCornerA 50 33 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 50 33, endpointRunWeightQ (endpointMeanCutoff 50 33) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 50 33) = (42773349/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 50 33 h = (logRoundedQ ((endpointMeanCutoff 50 33:ℚ)/200)).2+(42773349/125000000000000:ℚ)+((endpointMeanRuns 50 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 50 33).map (fun r => endpointRunWeightQ (endpointMeanCutoff 50 33) r*endpointJoint24Q (endpointMeanCornerK 50 33 h) (endpointMeanCornerA 50 33 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 50 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 50 33 h≤endpointMeanCorner 50 33 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 50 33 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint50_33

namespace EndpointAnalyticJoint50_34
private noncomputable def weights : IntegerLookupTree := (.leaf (103700609300000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2880473459782649:ℤ)), (.leaf (2895875698788780:ℤ)), (.leaf (3004928331427966:ℤ)), (.leaf (3022287081401510:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 50 34) 8000 (endpointMeanRuns 50 34) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 50 34, EndpointRunConditions (endpointMeanCutoff 50 34) (endpointMeanBox 50 34).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 34, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 50 34 h) (endpointMeanCornerA 50 34 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 34, endpointJoint24Q (endpointMeanCornerK 50 34 h) (endpointMeanCornerA 50 34 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 50 34, endpointRunWeightQ (endpointMeanCutoff 50 34) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 50 34) = (341501863/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 50 34 h = (logRoundedQ ((endpointMeanCutoff 50 34:ℚ)/200)).2+(341501863/1000000000000000:ℚ)+((endpointMeanRuns 50 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 50 34).map (fun r => endpointRunWeightQ (endpointMeanCutoff 50 34) r*endpointJoint24Q (endpointMeanCornerK 50 34 h) (endpointMeanCornerA 50 34 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 50 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 50 34 h≤endpointMeanCorner 50 34 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 50 34 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint50_34

namespace EndpointAnalyticJoint50_35
private noncomputable def weights : IntegerLookupTree := (.leaf (102263892700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2895875698788780:ℤ)), (.leaf (2926927690066150:ℤ)), (.leaf (3022287081401510:ℤ)), (.leaf (3057305992627403:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 50 35) 8000 (endpointMeanRuns 50 35) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 50 35, EndpointRunConditions (endpointMeanCutoff 50 35) (endpointMeanBox 50 35).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 35, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 50 35 h) (endpointMeanCornerA 50 35 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 35, endpointJoint24Q (endpointMeanCornerK 50 35 h) (endpointMeanCornerA 50 35 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 50 35, endpointRunWeightQ (endpointMeanCutoff 50 35) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 50 35) = (42626889/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 50 35 h = (logRoundedQ ((endpointMeanCutoff 50 35:ℚ)/200)).2+(42626889/125000000000000:ℚ)+((endpointMeanRuns 50 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 50 35).map (fun r => endpointRunWeightQ (endpointMeanCutoff 50 35) r*endpointJoint24Q (endpointMeanCornerK 50 35 h) (endpointMeanCornerA 50 35 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 50 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 50 35 h≤endpointMeanCorner 50 35 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 50 35 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint50_35

namespace EndpointAnalyticJoint50_36
private noncomputable def weights : IntegerLookupTree := (.leaf (100007368400000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2926927690066150:ℤ)), (.leaf (2974131101184460:ℤ)), (.leaf (3057305992627403:ℤ)), (.leaf (3110596627146050:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 50 36) 8000 (endpointMeanRuns 50 36) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 50 36, EndpointRunConditions (endpointMeanCutoff 50 36) (endpointMeanBox 50 36).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 36, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 50 36 h) (endpointMeanCornerA 50 36 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 36, endpointJoint24Q (endpointMeanCornerK 50 36 h) (endpointMeanCornerA 50 36 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 50 36, endpointRunWeightQ (endpointMeanCutoff 50 36) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 50 36) = (68048113/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 50 36 h = (logRoundedQ ((endpointMeanCutoff 50 36:ℚ)/200)).2+(68048113/200000000000000:ℚ)+((endpointMeanRuns 50 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 50 36).map (fun r => endpointRunWeightQ (endpointMeanCutoff 50 36) r*endpointJoint24Q (endpointMeanCornerK 50 36 h) (endpointMeanCornerA 50 36 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 50 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 50 36 h≤endpointMeanCorner 50 36 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 50 36 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint50_36

namespace EndpointAnalyticJoint50_37
private noncomputable def weights : IntegerLookupTree := (.leaf (97258153100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2974131101184460:ℤ)), (.leaf (3022095775394014:ℤ)), (.leaf (3110596627146050:ℤ)), (.leaf (3164816148643702:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 50 37) 8000 (endpointMeanRuns 50 37) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 50 37, EndpointRunConditions (endpointMeanCutoff 50 37) (endpointMeanBox 50 37).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 37, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 50 37 h) (endpointMeanCornerA 50 37 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 50 37, endpointJoint24Q (endpointMeanCornerK 50 37 h) (endpointMeanCornerA 50 37 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 50 37, endpointRunWeightQ (endpointMeanCutoff 50 37) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 50 37) = (339279653/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 50 37 h = (logRoundedQ ((endpointMeanCutoff 50 37:ℚ)/200)).2+(339279653/1000000000000000:ℚ)+((endpointMeanRuns 50 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 50 37).map (fun r => endpointRunWeightQ (endpointMeanCutoff 50 37) r*endpointJoint24Q (endpointMeanCornerK 50 37 h) (endpointMeanCornerA 50 37 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 50 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 50 37 h≤endpointMeanCorner 50 37 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 50 37 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint50_37

namespace EndpointAnalyticJoint51_27
private noncomputable def weights : IntegerLookupTree := (.leaf (112136943900000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2754377525651268:ℤ)), (.leaf (2756196472053774:ℤ)), (.leaf (2875514136289690:ℤ)), (.leaf (2877582287474533:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 51 27) 8000 (endpointMeanRuns 51 27) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 51 27, EndpointRunConditions (endpointMeanCutoff 51 27) (endpointMeanBox 51 27).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 27, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 51 27 h) (endpointMeanCornerA 51 27 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 27, endpointJoint24Q (endpointMeanCornerK 51 27 h) (endpointMeanCornerA 51 27 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 51 27, endpointRunWeightQ (endpointMeanCutoff 51 27) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 51 27) = (2754131/8000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 51 27 h = (logRoundedQ ((endpointMeanCutoff 51 27:ℚ)/200)).2+(2754131/8000000000000:ℚ)+((endpointMeanRuns 51 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 51 27).map (fun r => endpointRunWeightQ (endpointMeanCutoff 51 27) r*endpointJoint24Q (endpointMeanCornerK 51 27 h) (endpointMeanCornerA 51 27 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 51 27).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 51 27 h≤endpointMeanCorner 51 27 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 51 27 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint51_27

namespace EndpointAnalyticJoint51_28
private noncomputable def weights : IntegerLookupTree := (.leaf (110580463300000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2756196472053774:ℤ)), (.leaf (2804238591229282:ℤ)), (.leaf (2877582287474533:ℤ)), (.leaf (2932250207795968:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 51 28) 8000 (endpointMeanRuns 51 28) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 51 28, EndpointRunConditions (endpointMeanCutoff 51 28) (endpointMeanBox 51 28).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 28, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 51 28 h) (endpointMeanCornerA 51 28 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 28, endpointJoint24Q (endpointMeanCornerK 51 28 h) (endpointMeanCornerA 51 28 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 51 28, endpointRunWeightQ (endpointMeanCutoff 51 28) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 51 28) = (171883909/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 51 28 h = (logRoundedQ ((endpointMeanCutoff 51 28:ℚ)/200)).2+(171883909/500000000000000:ℚ)+((endpointMeanRuns 51 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 51 28).map (fun r => endpointRunWeightQ (endpointMeanCutoff 51 28) r*endpointJoint24Q (endpointMeanCornerK 51 28 h) (endpointMeanCornerA 51 28 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 51 28).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 51 28 h≤endpointMeanCorner 51 28 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 51 28 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint51_28

namespace EndpointAnalyticJoint51_29
private noncomputable def weights : IntegerLookupTree := (.leaf (108135975700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2804238591229282:ℤ)), (.leaf (2833464887311356:ℤ)), (.leaf (2932250207795968:ℤ)), (.leaf (2965548220959884:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 51 29) 8000 (endpointMeanRuns 51 29) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 51 29, EndpointRunConditions (endpointMeanCutoff 51 29) (endpointMeanBox 51 29).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 29, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 51 29 h) (endpointMeanCornerA 51 29 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 29, endpointJoint24Q (endpointMeanCornerK 51 29 h) (endpointMeanCornerA 51 29 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 51 29, endpointRunWeightQ (endpointMeanCutoff 51 29) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 51 29) = (342974591/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 51 29 h = (logRoundedQ ((endpointMeanCutoff 51 29:ℚ)/200)).2+(342974591/1000000000000000:ℚ)+((endpointMeanRuns 51 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 51 29).map (fun r => endpointRunWeightQ (endpointMeanCutoff 51 29) r*endpointJoint24Q (endpointMeanCornerK 51 29 h) (endpointMeanCornerA 51 29 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 51 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 51 29 h≤endpointMeanCorner 51 29 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 51 29 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint51_29

namespace EndpointAnalyticJoint51_30
private noncomputable def weights : IntegerLookupTree := (.leaf (106636339700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2833464887311356:ℤ)), (.leaf (2853118112686622:ℤ)), (.leaf (2965548220959884:ℤ)), (.leaf (2987956701896959:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 51 30) 8000 (endpointMeanRuns 51 30) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 51 30, EndpointRunConditions (endpointMeanCutoff 51 30) (endpointMeanBox 51 30).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 30, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 51 30 h) (endpointMeanCornerA 51 30 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 30, endpointJoint24Q (endpointMeanCornerK 51 30 h) (endpointMeanCornerA 51 30 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 51 30, endpointRunWeightQ (endpointMeanCutoff 51 30) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 51 30) = (68496317/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 51 30 h = (logRoundedQ ((endpointMeanCutoff 51 30:ℚ)/200)).2+(68496317/200000000000000:ℚ)+((endpointMeanRuns 51 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 51 30).map (fun r => endpointRunWeightQ (endpointMeanCutoff 51 30) r*endpointJoint24Q (endpointMeanCornerK 51 30 h) (endpointMeanCornerA 51 30 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 51 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 51 30 h≤endpointMeanCorner 51 30 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 51 30 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint51_30

namespace EndpointAnalyticJoint51_31
private noncomputable def weights : IntegerLookupTree := (.leaf (104572537800000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2853118112686622:ℤ)), (.leaf (2902849632838139:ℤ)), (.leaf (2987956701896959:ℤ)), (.leaf (3044721500462139:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 51 31) 8000 (endpointMeanRuns 51 31) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 51 31, EndpointRunConditions (endpointMeanCutoff 51 31) (endpointMeanBox 51 31).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 31, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 51 31 h) (endpointMeanCornerA 51 31 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 31, endpointJoint24Q (endpointMeanCornerK 51 31 h) (endpointMeanCornerA 51 31 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 51 31, endpointRunWeightQ (endpointMeanCutoff 51 31) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 51 31) = (68358981/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 51 31 h = (logRoundedQ ((endpointMeanCutoff 51 31:ℚ)/200)).2+(68358981/200000000000000:ℚ)+((endpointMeanRuns 51 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 51 31).map (fun r => endpointRunWeightQ (endpointMeanCutoff 51 31) r*endpointJoint24Q (endpointMeanCornerK 51 31 h) (endpointMeanCornerA 51 31 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 51 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 51 31 h≤endpointMeanCorner 51 31 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 51 31 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint51_31

namespace EndpointAnalyticJoint51_32
private noncomputable def weights : IntegerLookupTree := (.leaf (101694923500000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2902849632838139:ℤ)), (.leaf (2953448002520204:ℤ)), (.leaf (3044721500462139:ℤ)), (.leaf (3102564709017026:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 51 32) 8000 (endpointMeanRuns 51 32) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 51 32, EndpointRunConditions (endpointMeanCutoff 51 32) (endpointMeanBox 51 32).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 32, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 51 32 h) (endpointMeanCornerA 51 32 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 32, endpointJoint24Q (endpointMeanCornerK 51 32 h) (endpointMeanCornerA 51 32 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 51 32, endpointRunWeightQ (endpointMeanCutoff 51 32) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 51 32) = (170410493/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 51 32 h = (logRoundedQ ((endpointMeanCutoff 51 32:ℚ)/200)).2+(170410493/500000000000000:ℚ)+((endpointMeanRuns 51 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 51 32).map (fun r => endpointRunWeightQ (endpointMeanCutoff 51 32) r*endpointJoint24Q (endpointMeanCornerK 51 32 h) (endpointMeanCornerA 51 32 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 51 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 51 32 h≤endpointMeanCorner 51 32 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 51 32 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint51_32

namespace EndpointAnalyticJoint51_33
private noncomputable def weights : IntegerLookupTree := (.leaf (98622965200000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2953448002520204:ℤ)), (.leaf (3004928331427966:ℤ)), (.leaf (3102564709017026:ℤ)), (.leaf (3161506815049206:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 51 33) 8000 (endpointMeanRuns 51 33) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 51 33, EndpointRunConditions (endpointMeanCutoff 51 33) (endpointMeanBox 51 33).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 33, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 51 33 h) (endpointMeanCornerA 51 33 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 33, endpointJoint24Q (endpointMeanCornerK 51 33 h) (endpointMeanCornerA 51 33 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 51 33, endpointRunWeightQ (endpointMeanCutoff 51 33) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 51 33) = (169879553/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 51 33 h = (logRoundedQ ((endpointMeanCutoff 51 33:ℚ)/200)).2+(169879553/500000000000000:ℚ)+((endpointMeanRuns 51 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 51 33).map (fun r => endpointRunWeightQ (endpointMeanCutoff 51 33) r*endpointJoint24Q (endpointMeanCornerK 51 33 h) (endpointMeanCornerA 51 33 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 51 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 51 33 h≤endpointMeanCorner 51 33 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 51 33 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint51_33

namespace EndpointAnalyticJoint51_34
private noncomputable def weights : IntegerLookupTree := (.leaf (96987516200000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3004928331427966:ℤ)), (.leaf (3022287081401510:ℤ)), (.leaf (3161506815049206:ℤ)), (.leaf (3181401980132260:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 51 34) 8000 (endpointMeanRuns 51 34) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 51 34, EndpointRunConditions (endpointMeanCutoff 51 34) (endpointMeanBox 51 34).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 34, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 51 34 h) (endpointMeanCornerA 51 34 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 34, endpointJoint24Q (endpointMeanCornerK 51 34 h) (endpointMeanCornerA 51 34 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 51 34, endpointRunWeightQ (endpointMeanCutoff 51 34) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 51 34) = (339184001/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 51 34 h = (logRoundedQ ((endpointMeanCutoff 51 34:ℚ)/200)).2+(339184001/1000000000000000:ℚ)+((endpointMeanRuns 51 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 51 34).map (fun r => endpointRunWeightQ (endpointMeanCutoff 51 34) r*endpointJoint24Q (endpointMeanCornerK 51 34 h) (endpointMeanCornerA 51 34 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 51 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 51 34 h≤endpointMeanCorner 51 34 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 51 34 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint51_34

namespace EndpointAnalyticJoint51_35
private noncomputable def weights : IntegerLookupTree := (.leaf (95645834700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3022287081401510:ℤ)), (.leaf (3057305992627403:ℤ)), (.leaf (3181401980132260:ℤ)), (.leaf (3221568695264794:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 51 35) 8000 (endpointMeanRuns 51 35) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 51 35, EndpointRunConditions (endpointMeanCutoff 51 35) (endpointMeanBox 51 35).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 35, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 51 35 h) (endpointMeanCornerA 51 35 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 35, endpointJoint24Q (endpointMeanCornerK 51 35 h) (endpointMeanCornerA 51 35 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 51 35, endpointRunWeightQ (endpointMeanCutoff 51 35) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 51 35) = (84676733/250000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 51 35 h = (logRoundedQ ((endpointMeanCutoff 51 35:ℚ)/200)).2+(84676733/250000000000000:ℚ)+((endpointMeanRuns 51 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 51 35).map (fun r => endpointRunWeightQ (endpointMeanCutoff 51 35) r*endpointJoint24Q (endpointMeanCornerK 51 35 h) (endpointMeanCornerA 51 35 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 51 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 51 35 h≤endpointMeanCorner 51 35 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 51 35 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint51_35

namespace EndpointAnalyticJoint51_36
private noncomputable def weights : IntegerLookupTree := (.leaf (93278413800000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3057305992627403:ℤ)), (.leaf (3110596627146050:ℤ)), (.leaf (3221568695264794:ℤ)), (.leaf (3282771622982753:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 51 36) 8000 (endpointMeanRuns 51 36) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 51 36, EndpointRunConditions (endpointMeanCutoff 51 36) (endpointMeanBox 51 36).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 36, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 51 36 h) (endpointMeanCornerA 51 36 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 36, endpointJoint24Q (endpointMeanCornerK 51 36 h) (endpointMeanCornerA 51 36 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 51 36, endpointRunWeightQ (endpointMeanCutoff 51 36) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 51 36) = (168926579/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 51 36 h = (logRoundedQ ((endpointMeanCutoff 51 36:ℚ)/200)).2+(168926579/500000000000000:ℚ)+((endpointMeanRuns 51 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 51 36).map (fun r => endpointRunWeightQ (endpointMeanCutoff 51 36) r*endpointJoint24Q (endpointMeanCornerK 51 36 h) (endpointMeanCornerA 51 36 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 51 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 51 36 h≤endpointMeanCorner 51 36 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 51 36 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint51_36

namespace EndpointAnalyticJoint51_37
private noncomputable def weights : IntegerLookupTree := (.leaf (90718062500000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3110596627146050:ℤ)), (.leaf (3164816148643702:ℤ)), (.leaf (3282771622982753:ℤ)), (.leaf (3345137275669685:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 51 37) 8000 (endpointMeanRuns 51 37) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 51 37, EndpointRunConditions (endpointMeanCutoff 51 37) (endpointMeanBox 51 37).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 37, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 51 37 h) (endpointMeanCornerA 51 37 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 37, endpointJoint24Q (endpointMeanCornerK 51 37 h) (endpointMeanCornerA 51 37 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 51 37, endpointRunWeightQ (endpointMeanCutoff 51 37) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 51 37) = (336911889/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 51 37 h = (logRoundedQ ((endpointMeanCutoff 51 37:ℚ)/200)).2+(336911889/1000000000000000:ℚ)+((endpointMeanRuns 51 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 51 37).map (fun r => endpointRunWeightQ (endpointMeanCutoff 51 37) r*endpointJoint24Q (endpointMeanCornerK 51 37 h) (endpointMeanCornerA 51 37 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 51 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 51 37 h≤endpointMeanCorner 51 37 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 51 37 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint51_37

namespace EndpointAnalyticJoint51_38
private noncomputable def weights : IntegerLookupTree := (.leaf (88229449200000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3164816148643702:ℤ)), (.leaf (3219980748164582:ℤ)), (.leaf (3345137275669685:ℤ)), (.leaf (3408687742617782:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 51 38) 8000 (endpointMeanRuns 51 38) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 51 38, EndpointRunConditions (endpointMeanCutoff 51 38) (endpointMeanBox 51 38).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 38, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 51 38 h) (endpointMeanCornerA 51 38 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 51 38, endpointJoint24Q (endpointMeanCornerK 51 38 h) (endpointMeanCornerA 51 38 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 51 38, endpointRunWeightQ (endpointMeanCutoff 51 38) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 51 38) = (167989127/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 51 38 h = (logRoundedQ ((endpointMeanCutoff 51 38:ℚ)/200)).2+(167989127/500000000000000:ℚ)+((endpointMeanRuns 51 38).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 51 38).map (fun r => endpointRunWeightQ (endpointMeanCutoff 51 38) r*endpointJoint24Q (endpointMeanCornerK 51 38 h) (endpointMeanCornerA 51 38 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 51 38).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 51 38 h≤endpointMeanCorner 51 38 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 51 38 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint51_38

namespace EndpointAnalyticJoint52_29
private noncomputable def weights : IntegerLookupTree := (.leaf (100847535200000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2941092946444607:ℤ)), (.leaf (2965548220959884:ℤ)), (.leaf (3109033554210910:ℤ)), (.leaf (3137513116120021:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 52 29) 8000 (endpointMeanRuns 52 29) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 52 29, EndpointRunConditions (endpointMeanCutoff 52 29) (endpointMeanBox 52 29).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 29, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 52 29 h) (endpointMeanCornerA 52 29 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 29, endpointJoint24Q (endpointMeanCornerK 52 29 h) (endpointMeanCornerA 52 29 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 52 29, endpointRunWeightQ (endpointMeanCutoff 52 29) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 52 29) = (340530409/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 52 29 h = (logRoundedQ ((endpointMeanCutoff 52 29:ℚ)/200)).2+(340530409/1000000000000000:ℚ)+((endpointMeanRuns 52 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 52 29).map (fun r => endpointRunWeightQ (endpointMeanCutoff 52 29) r*endpointJoint24Q (endpointMeanCornerK 52 29 h) (endpointMeanCornerA 52 29 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 52 29).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 52 29 h≤endpointMeanCorner 52 29 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 52 29 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint52_29

namespace EndpointAnalyticJoint52_30
private noncomputable def weights : IntegerLookupTree := (.leaf (99728906600000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2965548220959884:ℤ)), (.leaf (2987956701896959:ℤ)), (.leaf (3137513116120021:ℤ)), (.leaf (3163629947949266:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 52 30) 8000 (endpointMeanRuns 52 30) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 52 30, EndpointRunConditions (endpointMeanCutoff 52 30) (endpointMeanBox 52 30).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 30, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 52 30 h) (endpointMeanCornerA 52 30 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 30, endpointJoint24Q (endpointMeanCornerK 52 30 h) (endpointMeanCornerA 52 30 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 52 30, endpointRunWeightQ (endpointMeanCutoff 52 30) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 52 30) = (21259007/62500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 52 30 h = (logRoundedQ ((endpointMeanCutoff 52 30:ℚ)/200)).2+(21259007/62500000000000:ℚ)+((endpointMeanRuns 52 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 52 30).map (fun r => endpointRunWeightQ (endpointMeanCutoff 52 30) r*endpointJoint24Q (endpointMeanCornerK 52 30 h) (endpointMeanCornerA 52 30 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 52 30).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 52 30 h≤endpointMeanCorner 52 30 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 52 30 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint52_30

namespace EndpointAnalyticJoint52_31
private noncomputable def weights : IntegerLookupTree := (.leaf (97801745500000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (2987956701896959:ℤ)), (.leaf (3044721500462139:ℤ)), (.leaf (3163629947949266:ℤ)), (.leaf (3229877106219565:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 52 31) 8000 (endpointMeanRuns 52 31) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 52 31, EndpointRunConditions (endpointMeanCutoff 52 31) (endpointMeanBox 52 31).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 31, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 52 31 h) (endpointMeanCornerA 52 31 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 31, endpointJoint24Q (endpointMeanCornerK 52 31 h) (endpointMeanCornerA 52 31 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 52 31, endpointRunWeightQ (endpointMeanCutoff 52 31) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 52 31) = (169735597/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 52 31 h = (logRoundedQ ((endpointMeanCutoff 52 31:ℚ)/200)).2+(169735597/500000000000000:ℚ)+((endpointMeanRuns 52 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 52 31).map (fun r => endpointRunWeightQ (endpointMeanCutoff 52 31) r*endpointJoint24Q (endpointMeanCornerK 52 31 h) (endpointMeanCornerA 52 31 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 52 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 52 31 h≤endpointMeanCorner 52 31 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 52 31 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint52_31

namespace EndpointAnalyticJoint52_32
private noncomputable def weights : IntegerLookupTree := (.leaf (94849947000000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3044721500462139:ℤ)), (.leaf (3102564709017026:ℤ)), (.leaf (3229877106219565:ℤ)), (.leaf (3297511495629753:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 52 32) 8000 (endpointMeanRuns 52 32) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 52 32, EndpointRunConditions (endpointMeanCutoff 52 32) (endpointMeanBox 52 32).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 32, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 52 32 h) (endpointMeanCornerA 52 32 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 32, endpointJoint24Q (endpointMeanCornerK 52 32 h) (endpointMeanCornerA 52 32 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 52 32, endpointRunWeightQ (endpointMeanCutoff 52 32) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 52 32) = (338421637/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 52 32 h = (logRoundedQ ((endpointMeanCutoff 52 32:ℚ)/200)).2+(338421637/1000000000000000:ℚ)+((endpointMeanRuns 52 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 52 32).map (fun r => endpointRunWeightQ (endpointMeanCutoff 52 32) r*endpointJoint24Q (endpointMeanCornerK 52 32 h) (endpointMeanCornerA 52 32 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 52 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 52 32 h≤endpointMeanCorner 52 32 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 52 32 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint52_32

namespace EndpointAnalyticJoint52_33
private noncomputable def weights : IntegerLookupTree := (.leaf (92245529100000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3102564709017026:ℤ)), (.leaf (3161506815049206:ℤ)), (.leaf (3297511495629753:ℤ)), (.leaf (3366562165127532:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 52 33) 8000 (endpointMeanRuns 52 33) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 52 33, EndpointRunConditions (endpointMeanCutoff 52 33) (endpointMeanBox 52 33).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 33, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 52 33 h) (endpointMeanCornerA 52 33 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 33, endpointJoint24Q (endpointMeanCornerK 52 33 h) (endpointMeanCornerA 52 33 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 52 33, endpointRunWeightQ (endpointMeanCutoff 52 33) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 52 33) = (337475727/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 52 33 h = (logRoundedQ ((endpointMeanCutoff 52 33:ℚ)/200)).2+(337475727/1000000000000000:ℚ)+((endpointMeanRuns 52 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 52 33).map (fun r => endpointRunWeightQ (endpointMeanCutoff 52 33) r*endpointJoint24Q (endpointMeanCornerK 52 33 h) (endpointMeanCornerA 52 33 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 52 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 52 33 h≤endpointMeanCorner 52 33 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 52 33 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint52_33

namespace EndpointAnalyticJoint52_34
private noncomputable def weights : IntegerLookupTree := (.leaf (90466007700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3161506815049206:ℤ)), (.leaf (3181401980132260:ℤ)), (.leaf (3366562165127532:ℤ)), (.leaf (3389898892045092:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 52 34) 8000 (endpointMeanRuns 52 34) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 52 34, EndpointRunConditions (endpointMeanCutoff 52 34) (endpointMeanBox 52 34).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 34, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 52 34 h) (endpointMeanCornerA 52 34 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 34, endpointJoint24Q (endpointMeanCornerK 52 34 h) (endpointMeanCornerA 52 34 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 52 34, endpointRunWeightQ (endpointMeanCutoff 52 34) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 52 34) = (42102273/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 52 34 h = (logRoundedQ ((endpointMeanCutoff 52 34:ℚ)/200)).2+(42102273/125000000000000:ℚ)+((endpointMeanRuns 52 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 52 34).map (fun r => endpointRunWeightQ (endpointMeanCutoff 52 34) r*endpointJoint24Q (endpointMeanCornerK 52 34 h) (endpointMeanCornerA 52 34 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 52 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 52 34 h≤endpointMeanCorner 52 34 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 52 34 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint52_34

namespace EndpointAnalyticJoint52_35
private noncomputable def weights : IntegerLookupTree := (.leaf (89216420300000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3181401980132260:ℤ)), (.leaf (3221568695264794:ℤ)), (.leaf (3389898892045092:ℤ)), (.leaf (3437058771952414:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 52 35) 8000 (endpointMeanRuns 52 35) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 52 35, EndpointRunConditions (endpointMeanCutoff 52 35) (endpointMeanBox 52 35).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 35, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 52 35 h) (endpointMeanCornerA 52 35 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 35, endpointJoint24Q (endpointMeanCornerK 52 35 h) (endpointMeanCornerA 52 35 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 52 35, endpointRunWeightQ (endpointMeanCutoff 52 35) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 52 35) = (840877/2500000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 52 35 h = (logRoundedQ ((endpointMeanCutoff 52 35:ℚ)/200)).2+(840877/2500000000000:ℚ)+((endpointMeanRuns 52 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 52 35).map (fun r => endpointRunWeightQ (endpointMeanCutoff 52 35) r*endpointJoint24Q (endpointMeanCornerK 52 35 h) (endpointMeanCornerA 52 35 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 52 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 52 35 h≤endpointMeanCorner 52 35 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 52 35 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint52_35

namespace EndpointAnalyticJoint52_36
private noncomputable def weights : IntegerLookupTree := (.leaf (87011393000000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3221568695264794:ℤ)), (.leaf (3282771622982753:ℤ)), (.leaf (3437058771952414:ℤ)), (.leaf (3509031594373521:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 52 36) 8000 (endpointMeanRuns 52 36) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 52 36, EndpointRunConditions (endpointMeanCutoff 52 36) (endpointMeanBox 52 36).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 36, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 52 36 h) (endpointMeanCornerA 52 36 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 36, endpointJoint24Q (endpointMeanCornerK 52 36 h) (endpointMeanCornerA 52 36 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 52 36, endpointRunWeightQ (endpointMeanCutoff 52 36) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 52 36) = (16775713/50000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 52 36 h = (logRoundedQ ((endpointMeanCutoff 52 36:ℚ)/200)).2+(16775713/50000000000000:ℚ)+((endpointMeanRuns 52 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 52 36).map (fun r => endpointRunWeightQ (endpointMeanCutoff 52 36) r*endpointJoint24Q (endpointMeanCornerK 52 36 h) (endpointMeanCornerA 52 36 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 52 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 52 36 h≤endpointMeanCorner 52 36 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 52 36 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint52_36

namespace EndpointAnalyticJoint52_37
private noncomputable def weights : IntegerLookupTree := (.leaf (84626513400000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3282771622982753:ℤ)), (.leaf (3345137275669685:ℤ)), (.leaf (3509031594373521:ℤ)), (.leaf (3582511544694085:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 52 37) 8000 (endpointMeanRuns 52 37) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 52 37, EndpointRunConditions (endpointMeanCutoff 52 37) (endpointMeanBox 52 37).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 37, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 52 37 h) (endpointMeanCornerA 52 37 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 37, endpointJoint24Q (endpointMeanCornerK 52 37 h) (endpointMeanCornerA 52 37 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 52 37, endpointRunWeightQ (endpointMeanCutoff 52 37) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 52 37) = (167295923/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 52 37 h = (logRoundedQ ((endpointMeanCutoff 52 37:ℚ)/200)).2+(167295923/500000000000000:ℚ)+((endpointMeanRuns 52 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 52 37).map (fun r => endpointRunWeightQ (endpointMeanCutoff 52 37) r*endpointJoint24Q (endpointMeanCornerK 52 37 h) (endpointMeanCornerA 52 37 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 52 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 52 37 h≤endpointMeanCorner 52 37 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 52 37 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint52_37

namespace EndpointAnalyticJoint52_38
private noncomputable def weights : IntegerLookupTree := (.leaf (82308299000000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3345137275669685:ℤ)), (.leaf (3408687742617782:ℤ)), (.leaf (3582511544694085:ℤ)), (.leaf (3657530182528245:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 52 38) 8000 (endpointMeanRuns 52 38) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 52 38, EndpointRunConditions (endpointMeanCutoff 52 38) (endpointMeanBox 52 38).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 38, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 52 38 h) (endpointMeanCornerA 52 38 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 52 38, endpointJoint24Q (endpointMeanCornerK 52 38 h) (endpointMeanCornerA 52 38 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 52 38, endpointRunWeightQ (endpointMeanCutoff 52 38) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 52 38) = (66735353/200000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 52 38 h = (logRoundedQ ((endpointMeanCutoff 52 38:ℚ)/200)).2+(66735353/200000000000000:ℚ)+((endpointMeanRuns 52 38).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 52 38).map (fun r => endpointRunWeightQ (endpointMeanCutoff 52 38) r*endpointJoint24Q (endpointMeanCornerK 52 38 h) (endpointMeanCornerA 52 38 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 52 38).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 52 38 h≤endpointMeanCorner 52 38 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 52 38 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint52_38

namespace EndpointAnalyticJoint53_31
private noncomputable def weights : IntegerLookupTree := (.leaf (90718062500000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3189432252612484:ℤ)), (.leaf (3229877106219565:ℤ)), (.leaf (3436806913667081:ℤ)), (.leaf (3485594059024032:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 31) 8000 (endpointMeanRuns 53 31) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 53 31, EndpointRunConditions (endpointMeanCutoff 53 31) (endpointMeanBox 53 31).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 31, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 53 31 h) (endpointMeanCornerA 53 31 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 31, endpointJoint24Q (endpointMeanCornerK 53 31 h) (endpointMeanCornerA 53 31 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 53 31, endpointRunWeightQ (endpointMeanCutoff 53 31) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 53 31) = (336911889/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 53 31 h = (logRoundedQ ((endpointMeanCutoff 53 31:ℚ)/200)).2+(336911889/1000000000000000:ℚ)+((endpointMeanRuns 53 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 53 31).map (fun r => endpointRunWeightQ (endpointMeanCutoff 53 31) r*endpointJoint24Q (endpointMeanCornerK 53 31 h) (endpointMeanCornerA 53 31 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 53 31).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 53 31 h≤endpointMeanCorner 53 31 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 53 31 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint53_31

namespace EndpointAnalyticJoint53_32
private noncomputable def weights : IntegerLookupTree := (.leaf (92519638500000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3116590007372910:ℤ)), (.leaf (3178702163054309:ℤ)), (.leaf (3335933233739932:ℤ)), (.leaf (3409889784374905:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 32) 8000 (endpointMeanRuns 53 32) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 53 32, EndpointRunConditions (endpointMeanCutoff 53 32) (endpointMeanBox 53 32).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 32, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 53 32 h) (endpointMeanCornerA 53 32 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 32, endpointJoint24Q (endpointMeanCornerK 53 32 h) (endpointMeanCornerA 53 32 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 53 32, endpointRunWeightQ (endpointMeanCutoff 53 32) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 53 32) = (42020547/125000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 53 32 h = (logRoundedQ ((endpointMeanCutoff 53 32:ℚ)/200)).2+(42020547/125000000000000:ℚ)+((endpointMeanRuns 53 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 53 32).map (fun r => endpointRunWeightQ (endpointMeanCutoff 53 32) r*endpointJoint24Q (endpointMeanCornerK 53 32 h) (endpointMeanCornerA 53 32 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 53 32).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 53 32 h≤endpointMeanCorner 53 32 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 53 32 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint53_32

namespace EndpointAnalyticJoint53_33
private noncomputable def weights : IntegerLookupTree := (.leaf (89757049700000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3178702163054309:ℤ)), (.leaf (3242052184439657:ℤ)), (.leaf (3409889784374905:ℤ)), (.leaf (3485485927591204:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 33) 8000 (endpointMeanRuns 53 33) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 53 33, EndpointRunConditions (endpointMeanCutoff 53 33) (endpointMeanBox 53 33).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 33, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 53 33 h) (endpointMeanCornerA 53 33 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 33, endpointJoint24Q (endpointMeanCornerK 53 33 h) (endpointMeanCornerA 53 33 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 53 33, endpointRunWeightQ (endpointMeanCutoff 53 33) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 53 33) = (335144407/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 53 33 h = (logRoundedQ ((endpointMeanCutoff 53 33:ℚ)/200)).2+(335144407/1000000000000000:ℚ)+((endpointMeanRuns 53 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 53 33).map (fun r => endpointRunWeightQ (endpointMeanCutoff 53 33) r*endpointJoint24Q (endpointMeanCornerK 53 33 h) (endpointMeanCornerA 53 33 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 53 33).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 53 33 h≤endpointMeanCorner 53 33 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 53 33 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint53_33

namespace EndpointAnalyticJoint53_34
private noncomputable def weights : IntegerLookupTree := (.leaf (88043035300000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3242052184439657:ℤ)), (.leaf (3263448189395925:ℤ)), (.leaf (3485485927591204:ℤ)), (.leaf (3511055255443009:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 34) 8000 (endpointMeanRuns 53 34) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 53 34, EndpointRunConditions (endpointMeanCutoff 53 34) (endpointMeanBox 53 34).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 34, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 53 34 h) (endpointMeanCornerA 53 34 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 34, endpointJoint24Q (endpointMeanCornerK 53 34 h) (endpointMeanCornerA 53 34 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 53 34, endpointRunWeightQ (endpointMeanCutoff 53 34) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 53 34) = (33450001/100000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 53 34 h = (logRoundedQ ((endpointMeanCutoff 53 34:ℚ)/200)).2+(33450001/100000000000000:ℚ)+((endpointMeanRuns 53 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 53 34).map (fun r => endpointRunWeightQ (endpointMeanCutoff 53 34) r*endpointJoint24Q (endpointMeanCornerK 53 34 h) (endpointMeanCornerA 53 34 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 53 34).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 53 34 h≤endpointMeanCorner 53 34 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 53 34 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint53_34

namespace EndpointAnalyticJoint53_35
private noncomputable def weights : IntegerLookupTree := (.leaf (86839227600000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3263448189395925:ℤ)), (.leaf (3306664741603336:ℤ)), (.leaf (3511055255443009:ℤ)), (.leaf (3562758012621026:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 35) 8000 (endpointMeanRuns 53 35) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 53 35, EndpointRunConditions (endpointMeanCutoff 53 35) (endpointMeanBox 53 35).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 35, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 53 35 h) (endpointMeanCornerA 53 35 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 35, endpointJoint24Q (endpointMeanCornerK 53 35 h) (endpointMeanCornerA 53 35 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 53 35, endpointRunWeightQ (endpointMeanCutoff 53 35) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 53 35) = (13361677/40000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 53 35 h = (logRoundedQ ((endpointMeanCutoff 53 35:ℚ)/200)).2+(13361677/40000000000000:ℚ)+((endpointMeanRuns 53 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 53 35).map (fun r => endpointRunWeightQ (endpointMeanCutoff 53 35) r*endpointJoint24Q (endpointMeanCornerK 53 35 h) (endpointMeanCornerA 53 35 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 53 35).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 53 35 h≤endpointMeanCorner 53 35 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 53 35 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint53_35

namespace EndpointAnalyticJoint53_36
private noncomputable def weights : IntegerLookupTree := (.leaf (84714533900000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3306664741603336:ℤ)), (.leaf (3372564996282579:ℤ)), (.leaf (3562758012621026:ℤ)), (.leaf (3641743194547217:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 36) 8000 (endpointMeanRuns 53 36) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 53 36, EndpointRunConditions (endpointMeanCutoff 53 36) (endpointMeanBox 53 36).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 36, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 53 36 h) (endpointMeanCornerA 53 36 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 36, endpointJoint24Q (endpointMeanCornerK 53 36 h) (endpointMeanCornerA 53 36 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 53 36, endpointRunWeightQ (endpointMeanCutoff 53 36) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 53 36) = (166610969/500000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 53 36 h = (logRoundedQ ((endpointMeanCutoff 53 36:ℚ)/200)).2+(166610969/500000000000000:ℚ)+((endpointMeanRuns 53 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 53 36).map (fun r => endpointRunWeightQ (endpointMeanCutoff 53 36) r*endpointJoint24Q (endpointMeanCornerK 53 36 h) (endpointMeanCornerA 53 36 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 53 36).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 53 36 h≤endpointMeanCorner 53 36 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 53 36 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint53_36

namespace EndpointAnalyticJoint53_37
private noncomputable def weights : IntegerLookupTree := (.leaf (86041697400000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3249622393402293:ℤ)), (.leaf (3311344159089268:ℤ)), (.leaf (3481606296059694:ℤ)), (.leaf (3554730681812240:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 37) 8000 (endpointMeanRuns 53 37) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 53 37, EndpointRunConditions (endpointMeanCutoff 53 37) (endpointMeanBox 53 37).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 37, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 53 37 h) (endpointMeanCornerA 53 37 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 37, endpointJoint24Q (endpointMeanCornerK 53 37 h) (endpointMeanCornerA 53 37 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 53 37, endpointRunWeightQ (endpointMeanCutoff 53 37) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 53 37) = (8307941/25000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 53 37 h = (logRoundedQ ((endpointMeanCutoff 53 37:ℚ)/200)).2+(8307941/25000000000000:ℚ)+((endpointMeanRuns 53 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 53 37).map (fun r => endpointRunWeightQ (endpointMeanCutoff 53 37) r*endpointJoint24Q (endpointMeanCornerK 53 37 h) (endpointMeanCornerA 53 37 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 53 37).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 53 37 h≤endpointMeanCorner 53 37 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 53 37 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint53_37

namespace EndpointAnalyticJoint53_38
private noncomputable def weights : IntegerLookupTree := (.leaf (83728685900000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3311344159089268:ℤ)), (.leaf (3374238238324803:ℤ)), (.leaf (3554730681812240:ℤ)), (.leaf (3629390903422424:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 38) 8000 (endpointMeanRuns 53 38) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 53 38, EndpointRunConditions (endpointMeanCutoff 53 38) (endpointMeanBox 53 38).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 38, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 53 38 h) (endpointMeanCornerA 53 38 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 38, endpointJoint24Q (endpointMeanCornerK 53 38 h) (endpointMeanCornerA 53 38 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 53 38, endpointRunWeightQ (endpointMeanCutoff 53 38) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 53 38) = (331420389/1000000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 53 38 h = (logRoundedQ ((endpointMeanCutoff 53 38:ℚ)/200)).2+(331420389/1000000000000000:ℚ)+((endpointMeanRuns 53 38).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 53 38).map (fun r => endpointRunWeightQ (endpointMeanCutoff 53 38) r*endpointJoint24Q (endpointMeanCornerK 53 38 h) (endpointMeanCornerA 53 38 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 53 38).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 53 38 h≤endpointMeanCorner 53 38 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 53 38 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint53_38

namespace EndpointAnalyticJoint53_39
private noncomputable def weights : IntegerLookupTree := (.leaf (81257521400000:ℤ))
private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![(.leaf (3374238238324803:ℤ)), (.leaf (3438326897468941:ℤ)), (.leaf (3629390903422424:ℤ)), (.leaf (3705619218142844:ℤ))]
private theorem cover : EndpointRunsCover (endpointMeanCutoff 53 39) 8000 (endpointMeanRuns 53 39) := by decide +kernel
private theorem domains : ∀r∈endpointMeanRuns 53 39, EndpointRunConditions (endpointMeanCutoff 53 39) (endpointMeanBox 53 39).top r := by
  simp only [EndpointRunConditions]
  decide +kernel
private theorem prefactorDomains : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 39, roundUpQ (endpointJoint24Argument (endpointMeanCornerK 53 39 h) (endpointMeanCornerA 53 39 h) ((r.rate:ℚ)/100))<26 := by
  simp only [endpointJoint24Argument,EndpointAnalyticLogs.lower_eq]
  decide +kernel
private theorem prefactorValues : ∀h : Fin 4, ∀r∈endpointMeanRuns 53 39, endpointJoint24Q (endpointMeanCornerK 53 39 h) (endpointMeanCornerA 53 39 h) ((r.rate:ℚ)/100) = fixedQ ((prefactors h).get r.rate) := by
  simp only [endpointJoint24Q,endpointJoint24Argument,EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]
  decide +kernel
private theorem weightValues : ∀r∈endpointMeanRuns 53 39, endpointRunWeightQ (endpointMeanCutoff 53 39) r = fixedQ (weights.get r.start) := by
  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]
  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
  decide +kernel
private theorem tailValue : endpointAnalyticTailQ (endpointMeanCutoff 53 39) = (13217657/40000000000000:ℚ) := by
  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]
  decide +kernel
private theorem totalValue : ∀h : Fin 4, endpointMeanNumericCorner 53 39 h = (logRoundedQ ((endpointMeanCutoff 53 39:ℚ)/200)).2+(13217657/40000000000000:ℚ)+((endpointMeanRuns 53 39).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate))).sum := by
  intro h
  have hm : (endpointMeanRuns 53 39).map (fun r => endpointRunWeightQ (endpointMeanCutoff 53 39) r*endpointJoint24Q (endpointMeanCornerK 53 39 h) (endpointMeanCornerA 53 39 h) ((r.rate:ℚ)/100)) =
      (endpointMeanRuns 53 39).map (fun r => fixedQ (weights.get r.start)*fixedQ ((prefactors h).get r.rate)) := by
    apply List.map_congr_left
    intro r hr
    rw [weightValues r hr,prefactorValues h r hr]
  unfold endpointMeanNumericCorner
  rw [hm,tailValue]
private theorem totals : ∀h : Fin 4, endpointMeanNumericCorner 53 39 h≤endpointMeanCorner 53 39 h := by
  simp only [totalValue,EndpointAnalyticLogs.upper_eq]
  decide +kernel
theorem conditions : EndpointJointNumericalConditions 53 39 := ⟨cover,domains,prefactorDomains,totals⟩
end EndpointAnalyticJoint53_39

private theorem activeIndices48 : ∀ai : Fin 42, endpointMeanActive 48 ai → ai∈
    ([24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow48 (ai : Fin 42) : endpointMeanActive 48 ai →
    EndpointJointNumericalConditions 48 ai := by
  intro hact
  have hi := activeIndices48 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint48_24.conditions
  · exact EndpointAnalyticJoint48_25.conditions
  · exact EndpointAnalyticJoint48_26.conditions
  · exact EndpointAnalyticJoint48_27.conditions
  · exact EndpointAnalyticJoint48_28.conditions
  · exact EndpointAnalyticJoint48_29.conditions
  · exact EndpointAnalyticJoint48_30.conditions
  · exact EndpointAnalyticJoint48_31.conditions
  · exact EndpointAnalyticJoint48_32.conditions
  · exact EndpointAnalyticJoint48_33.conditions
  · exact EndpointAnalyticJoint48_34.conditions
  · exact EndpointAnalyticJoint48_35.conditions
  · exact EndpointAnalyticJoint48_36.conditions

private theorem activeIndices49 : ∀ai : Fin 42, endpointMeanActive 49 ai → ai∈
    ([25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow49 (ai : Fin 42) : endpointMeanActive 49 ai →
    EndpointJointNumericalConditions 49 ai := by
  intro hact
  have hi := activeIndices49 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint49_25.conditions
  · exact EndpointAnalyticJoint49_26.conditions
  · exact EndpointAnalyticJoint49_27.conditions
  · exact EndpointAnalyticJoint49_28.conditions
  · exact EndpointAnalyticJoint49_29.conditions
  · exact EndpointAnalyticJoint49_30.conditions
  · exact EndpointAnalyticJoint49_31.conditions
  · exact EndpointAnalyticJoint49_32.conditions
  · exact EndpointAnalyticJoint49_33.conditions
  · exact EndpointAnalyticJoint49_34.conditions
  · exact EndpointAnalyticJoint49_35.conditions
  · exact EndpointAnalyticJoint49_36.conditions
  · exact EndpointAnalyticJoint49_37.conditions

private theorem activeIndices50 : ∀ai : Fin 42, endpointMeanActive 50 ai → ai∈
    ([26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow50 (ai : Fin 42) : endpointMeanActive 50 ai →
    EndpointJointNumericalConditions 50 ai := by
  intro hact
  have hi := activeIndices50 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint50_26.conditions
  · exact EndpointAnalyticJoint50_27.conditions
  · exact EndpointAnalyticJoint50_28.conditions
  · exact EndpointAnalyticJoint50_29.conditions
  · exact EndpointAnalyticJoint50_30.conditions
  · exact EndpointAnalyticJoint50_31.conditions
  · exact EndpointAnalyticJoint50_32.conditions
  · exact EndpointAnalyticJoint50_33.conditions
  · exact EndpointAnalyticJoint50_34.conditions
  · exact EndpointAnalyticJoint50_35.conditions
  · exact EndpointAnalyticJoint50_36.conditions
  · exact EndpointAnalyticJoint50_37.conditions

private theorem activeIndices51 : ∀ai : Fin 42, endpointMeanActive 51 ai → ai∈
    ([27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow51 (ai : Fin 42) : endpointMeanActive 51 ai →
    EndpointJointNumericalConditions 51 ai := by
  intro hact
  have hi := activeIndices51 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint51_27.conditions
  · exact EndpointAnalyticJoint51_28.conditions
  · exact EndpointAnalyticJoint51_29.conditions
  · exact EndpointAnalyticJoint51_30.conditions
  · exact EndpointAnalyticJoint51_31.conditions
  · exact EndpointAnalyticJoint51_32.conditions
  · exact EndpointAnalyticJoint51_33.conditions
  · exact EndpointAnalyticJoint51_34.conditions
  · exact EndpointAnalyticJoint51_35.conditions
  · exact EndpointAnalyticJoint51_36.conditions
  · exact EndpointAnalyticJoint51_37.conditions
  · exact EndpointAnalyticJoint51_38.conditions

private theorem activeIndices52 : ∀ai : Fin 42, endpointMeanActive 52 ai → ai∈
    ([29, 30, 31, 32, 33, 34, 35, 36, 37, 38] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow52 (ai : Fin 42) : endpointMeanActive 52 ai →
    EndpointJointNumericalConditions 52 ai := by
  intro hact
  have hi := activeIndices52 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint52_29.conditions
  · exact EndpointAnalyticJoint52_30.conditions
  · exact EndpointAnalyticJoint52_31.conditions
  · exact EndpointAnalyticJoint52_32.conditions
  · exact EndpointAnalyticJoint52_33.conditions
  · exact EndpointAnalyticJoint52_34.conditions
  · exact EndpointAnalyticJoint52_35.conditions
  · exact EndpointAnalyticJoint52_36.conditions
  · exact EndpointAnalyticJoint52_37.conditions
  · exact EndpointAnalyticJoint52_38.conditions

private theorem activeIndices53 : ∀ai : Fin 42, endpointMeanActive 53 ai → ai∈
    ([31, 32, 33, 34, 35, 36, 37, 38, 39] : List (Fin 42)) := by
  simp only [endpointMeanActive]
  decide +kernel
theorem endpointAnalyticRow53 (ai : Fin 42) : endpointMeanActive 53 ai →
    EndpointJointNumericalConditions 53 ai := by
  intro hact
  have hi := activeIndices53 ai hact
  fin_cases hi
  · exact EndpointAnalyticJoint53_31.conditions
  · exact EndpointAnalyticJoint53_32.conditions
  · exact EndpointAnalyticJoint53_33.conditions
  · exact EndpointAnalyticJoint53_34.conditions
  · exact EndpointAnalyticJoint53_35.conditions
  · exact EndpointAnalyticJoint53_36.conditions
  · exact EndpointAnalyticJoint53_37.conditions
  · exact EndpointAnalyticJoint53_38.conditions
  · exact EndpointAnalyticJoint53_39.conditions

end SingularValueBounds.KL.Certificates
