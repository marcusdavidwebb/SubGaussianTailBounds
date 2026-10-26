import SingularValueBounds.KL.Certificates.ConcreteMajorants.Row5.Block00
import SingularValueBounds.KL.Certificates.ConcreteMajorants.Row5.Block01
import SingularValueBounds.KL.Certificates.ConcreteMajorants.Row5.Block02
import SingularValueBounds.KL.Certificates.ConcreteMajorants.Row5.Block03
import SingularValueBounds.KL.Certificates.ConcreteMajorants.Row5.Block04
import SingularValueBounds.KL.Certificates.ConcreteMajorants.Row5.Block05
import SingularValueBounds.KL.Certificates.ConcreteMajorants.Row5.Block06
import SingularValueBounds.KL.Certificates.ConcreteMajorants.Row5.Block07
import SingularValueBounds.KL.Certificates.ConcreteMajorants.Row5.Block08
import SingularValueBounds.KL.Certificates.ConcreteMajorants.Row5.Block09

/-! All 70 leaf certificates for determinant majorant 5. -/
namespace SingularValueBounds.KL.Certificates
open MajorantRow5

theorem concrete_majorant_row_5 :
    ∀ leaf ∈ (majorantTrees 5).leaves (majorantBoxes 5),
      BoxCertificate (majorantQuotient 5) (majorantDegrees 5).1 (majorantDegrees 5).2 leaf := by
  intro leaf hc
  have htree : majorantTrees 5 = (.split (.split .leaf (.split .leaf (.split .leaf .leaf .leaf .leaf) .leaf (.split .leaf .leaf .leaf .leaf)) .leaf (.split .leaf .leaf .leaf .leaf)) (.split .leaf .leaf (.split (.split .leaf .leaf .leaf .leaf) .leaf (.split .leaf .leaf .leaf .leaf) .leaf) .leaf) .leaf (.split (.split (.split .leaf .leaf .leaf .leaf) (.split .leaf .leaf .leaf .leaf) .leaf (.split (.split .leaf .leaf .leaf .leaf) .leaf (.split .leaf .leaf .leaf .leaf) .leaf)) .leaf (.split .leaf (.split .leaf (.split .leaf .leaf .leaf .leaf) .leaf (.split .leaf .leaf .leaf .leaf)) .leaf .leaf) (.split .leaf .leaf (.split .leaf .leaf .leaf .leaf) .leaf))) := by rfl
  have hbox : majorantBoxes 5 = ⟨(1/4), (51/100), (0/1), (13/20)⟩ := by rfl
  have hdegree : majorantDegrees 5 = (8, 13) := by rfl
  rw [htree, hbox] at hc
  rw [hdegree]
  have hleaves : ((.split (.split .leaf (.split .leaf (.split .leaf .leaf .leaf .leaf) .leaf (.split .leaf .leaf .leaf .leaf)) .leaf (.split .leaf .leaf .leaf .leaf)) (.split .leaf .leaf (.split (.split .leaf .leaf .leaf .leaf) .leaf (.split .leaf .leaf .leaf .leaf) .leaf) .leaf) .leaf (.split (.split (.split .leaf .leaf .leaf .leaf) (.split .leaf .leaf .leaf .leaf) .leaf (.split (.split .leaf .leaf .leaf .leaf) .leaf (.split .leaf .leaf .leaf .leaf) .leaf)) .leaf (.split .leaf (.split .leaf (.split .leaf .leaf .leaf .leaf) .leaf (.split .leaf .leaf .leaf .leaf)) .leaf .leaf) (.split .leaf .leaf (.split .leaf .leaf .leaf .leaf) .leaf))) : QuadTree).leaves ⟨(1/4), (51/100), (0/1), (13/20)⟩ =
      [⟨(1/4), (63/200), (0/1), (13/80)⟩,
      ⟨(1/4), (113/400), (13/80), (39/160)⟩,
      ⟨(1/4), (213/800), (39/160), (91/320)⟩,
      ⟨(1/4), (213/800), (91/320), (13/40)⟩,
      ⟨(213/800), (113/400), (39/160), (91/320)⟩,
      ⟨(213/800), (113/400), (91/320), (13/40)⟩,
      ⟨(113/400), (63/200), (13/80), (39/160)⟩,
      ⟨(113/400), (239/800), (39/160), (91/320)⟩,
      ⟨(113/400), (239/800), (91/320), (13/40)⟩,
      ⟨(239/800), (63/200), (39/160), (91/320)⟩,
      ⟨(239/800), (63/200), (91/320), (13/40)⟩,
      ⟨(63/200), (19/50), (0/1), (13/80)⟩,
      ⟨(63/200), (139/400), (13/80), (39/160)⟩,
      ⟨(63/200), (139/400), (39/160), (13/40)⟩,
      ⟨(139/400), (19/50), (13/80), (39/160)⟩,
      ⟨(139/400), (19/50), (39/160), (13/40)⟩,
      ⟨(1/4), (63/200), (13/40), (39/80)⟩,
      ⟨(1/4), (63/200), (39/80), (13/20)⟩,
      ⟨(63/200), (53/160), (13/40), (117/320)⟩,
      ⟨(63/200), (53/160), (117/320), (13/32)⟩,
      ⟨(53/160), (139/400), (13/40), (117/320)⟩,
      ⟨(53/160), (139/400), (117/320), (13/32)⟩,
      ⟨(63/200), (139/400), (13/32), (39/80)⟩,
      ⟨(139/400), (291/800), (13/40), (117/320)⟩,
      ⟨(139/400), (291/800), (117/320), (13/32)⟩,
      ⟨(291/800), (19/50), (13/40), (117/320)⟩,
      ⟨(291/800), (19/50), (117/320), (13/32)⟩,
      ⟨(139/400), (19/50), (13/32), (39/80)⟩,
      ⟨(63/200), (19/50), (39/80), (13/20)⟩,
      ⟨(19/50), (51/100), (0/1), (13/40)⟩,
      ⟨(19/50), (317/800), (13/40), (117/320)⟩,
      ⟨(19/50), (317/800), (117/320), (13/32)⟩,
      ⟨(317/800), (33/80), (13/40), (117/320)⟩,
      ⟨(317/800), (33/80), (117/320), (13/32)⟩,
      ⟨(19/50), (317/800), (13/32), (143/320)⟩,
      ⟨(19/50), (317/800), (143/320), (39/80)⟩,
      ⟨(317/800), (33/80), (13/32), (143/320)⟩,
      ⟨(317/800), (33/80), (143/320), (39/80)⟩,
      ⟨(33/80), (89/200), (13/40), (13/32)⟩,
      ⟨(33/80), (673/1600), (13/32), (273/640)⟩,
      ⟨(33/80), (673/1600), (273/640), (143/320)⟩,
      ⟨(673/1600), (343/800), (13/32), (273/640)⟩,
      ⟨(673/1600), (343/800), (273/640), (143/320)⟩,
      ⟨(33/80), (343/800), (143/320), (39/80)⟩,
      ⟨(343/800), (699/1600), (13/32), (273/640)⟩,
      ⟨(343/800), (699/1600), (273/640), (143/320)⟩,
      ⟨(699/1600), (89/200), (13/32), (273/640)⟩,
      ⟨(699/1600), (89/200), (273/640), (143/320)⟩,
      ⟨(343/800), (89/200), (143/320), (39/80)⟩,
      ⟨(19/50), (89/200), (39/80), (13/20)⟩,
      ⟨(89/200), (191/400), (13/40), (13/32)⟩,
      ⟨(89/200), (369/800), (13/32), (143/320)⟩,
      ⟨(89/200), (29/64), (143/320), (299/640)⟩,
      ⟨(89/200), (29/64), (299/640), (39/80)⟩,
      ⟨(29/64), (369/800), (143/320), (299/640)⟩,
      ⟨(29/64), (369/800), (299/640), (39/80)⟩,
      ⟨(369/800), (191/400), (13/32), (143/320)⟩,
      ⟨(369/800), (751/1600), (143/320), (299/640)⟩,
      ⟨(369/800), (751/1600), (299/640), (39/80)⟩,
      ⟨(751/1600), (191/400), (143/320), (299/640)⟩,
      ⟨(751/1600), (191/400), (299/640), (39/80)⟩,
      ⟨(191/400), (51/100), (13/40), (13/32)⟩,
      ⟨(191/400), (51/100), (13/32), (39/80)⟩,
      ⟨(89/200), (191/400), (39/80), (91/160)⟩,
      ⟨(89/200), (191/400), (91/160), (13/20)⟩,
      ⟨(191/400), (79/160), (39/80), (169/320)⟩,
      ⟨(191/400), (79/160), (169/320), (91/160)⟩,
      ⟨(79/160), (51/100), (39/80), (169/320)⟩,
      ⟨(79/160), (51/100), (169/320), (91/160)⟩,
      ⟨(191/400), (51/100), (91/160), (13/20)⟩] := by
    norm_num [QuadTree.leaves, RationalBox.child]
  rw [hleaves] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact majorant_5_leaf_0
  · exact majorant_5_leaf_1
  · exact majorant_5_leaf_2
  · exact majorant_5_leaf_3
  · exact majorant_5_leaf_4
  · exact majorant_5_leaf_5
  · exact majorant_5_leaf_6
  · exact majorant_5_leaf_7
  · exact majorant_5_leaf_8
  · exact majorant_5_leaf_9
  · exact majorant_5_leaf_10
  · exact majorant_5_leaf_11
  · exact majorant_5_leaf_12
  · exact majorant_5_leaf_13
  · exact majorant_5_leaf_14
  · exact majorant_5_leaf_15
  · exact majorant_5_leaf_16
  · exact majorant_5_leaf_17
  · exact majorant_5_leaf_18
  · exact majorant_5_leaf_19
  · exact majorant_5_leaf_20
  · exact majorant_5_leaf_21
  · exact majorant_5_leaf_22
  · exact majorant_5_leaf_23
  · exact majorant_5_leaf_24
  · exact majorant_5_leaf_25
  · exact majorant_5_leaf_26
  · exact majorant_5_leaf_27
  · exact majorant_5_leaf_28
  · exact majorant_5_leaf_29
  · exact majorant_5_leaf_30
  · exact majorant_5_leaf_31
  · exact majorant_5_leaf_32
  · exact majorant_5_leaf_33
  · exact majorant_5_leaf_34
  · exact majorant_5_leaf_35
  · exact majorant_5_leaf_36
  · exact majorant_5_leaf_37
  · exact majorant_5_leaf_38
  · exact majorant_5_leaf_39
  · exact majorant_5_leaf_40
  · exact majorant_5_leaf_41
  · exact majorant_5_leaf_42
  · exact majorant_5_leaf_43
  · exact majorant_5_leaf_44
  · exact majorant_5_leaf_45
  · exact majorant_5_leaf_46
  · exact majorant_5_leaf_47
  · exact majorant_5_leaf_48
  · exact majorant_5_leaf_49
  · exact majorant_5_leaf_50
  · exact majorant_5_leaf_51
  · exact majorant_5_leaf_52
  · exact majorant_5_leaf_53
  · exact majorant_5_leaf_54
  · exact majorant_5_leaf_55
  · exact majorant_5_leaf_56
  · exact majorant_5_leaf_57
  · exact majorant_5_leaf_58
  · exact majorant_5_leaf_59
  · exact majorant_5_leaf_60
  · exact majorant_5_leaf_61
  · exact majorant_5_leaf_62
  · exact majorant_5_leaf_63
  · exact majorant_5_leaf_64
  · exact majorant_5_leaf_65
  · exact majorant_5_leaf_66
  · exact majorant_5_leaf_67
  · exact majorant_5_leaf_68
  · exact majorant_5_leaf_69

end SingularValueBounds.KL.Certificates
