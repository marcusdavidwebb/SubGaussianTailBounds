import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block00
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block01
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block02
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block03
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block04
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block05
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block06
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block07
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block08
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block09
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block10
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block11
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block12
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block13
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block14
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block15
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block16
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block17
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanRows.Block18

/-! Kernel-checked polynomial, scalar, and coverage conditions for all 1,330 cells. -/
namespace SingularValueBounds.KL.Certificates

theorem generalMeanRowConditions (i : Fin 1330) :
    GeneralMeanRowConditions (generalMeanRows i) := by
  have hb (b : Fin 19) (j : Fin 70) :
      GeneralMeanRowConditions (generalMeanRowBlocks b j) := by
    fin_cases b
    · exact generalMeanRowBlockConditions_0 j
    · exact generalMeanRowBlockConditions_1 j
    · exact generalMeanRowBlockConditions_2 j
    · exact generalMeanRowBlockConditions_3 j
    · exact generalMeanRowBlockConditions_4 j
    · exact generalMeanRowBlockConditions_5 j
    · exact generalMeanRowBlockConditions_6 j
    · exact generalMeanRowBlockConditions_7 j
    · exact generalMeanRowBlockConditions_8 j
    · exact generalMeanRowBlockConditions_9 j
    · exact generalMeanRowBlockConditions_10 j
    · exact generalMeanRowBlockConditions_11 j
    · exact generalMeanRowBlockConditions_12 j
    · exact generalMeanRowBlockConditions_13 j
    · exact generalMeanRowBlockConditions_14 j
    · exact generalMeanRowBlockConditions_15 j
    · exact generalMeanRowBlockConditions_16 j
    · exact generalMeanRowBlockConditions_17 j
    · exact generalMeanRowBlockConditions_18 j
  exact hb _ _

theorem generalMeanCellConditions : GeneralMeanCellConditions :=
  ⟨generalMeanAPartition_valid, generalMeanClippedTrees_valid, generalMeanRowConditions⟩

end SingularValueBounds.KL.Certificates
