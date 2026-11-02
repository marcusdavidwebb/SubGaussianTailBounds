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
  have hb : ∀ b : Fin 19, ∀ j : Fin 70,
      GeneralMeanRowConditions (generalMeanRowBlocks b j) :=
    Fin.cases (motive := fun b => ∀ j : Fin 70,
      GeneralMeanRowConditions (generalMeanRowBlocks b j))
      generalMeanRowBlockConditions_0 <|
      Fin.cases generalMeanRowBlockConditions_1 <|
      Fin.cases generalMeanRowBlockConditions_2 <|
      Fin.cases generalMeanRowBlockConditions_3 <|
      Fin.cases generalMeanRowBlockConditions_4 <|
      Fin.cases generalMeanRowBlockConditions_5 <|
      Fin.cases generalMeanRowBlockConditions_6 <|
      Fin.cases generalMeanRowBlockConditions_7 <|
      Fin.cases generalMeanRowBlockConditions_8 <|
      Fin.cases generalMeanRowBlockConditions_9 <|
      Fin.cases generalMeanRowBlockConditions_10 <|
      Fin.cases generalMeanRowBlockConditions_11 <|
      Fin.cases generalMeanRowBlockConditions_12 <|
      Fin.cases generalMeanRowBlockConditions_13 <|
      Fin.cases generalMeanRowBlockConditions_14 <|
      Fin.cases generalMeanRowBlockConditions_15 <|
      Fin.cases generalMeanRowBlockConditions_16 <|
      Fin.cases generalMeanRowBlockConditions_17 <|
      Fin.cases generalMeanRowBlockConditions_18 <|
      fun b => Fin.elim0 b
  exact hb _ _

theorem generalMeanCellConditions : GeneralMeanCellConditions :=
  ⟨generalMeanAPartition_valid, generalMeanClippedTrees_valid, generalMeanRowConditions⟩

end SingularValueBounds.KL.Certificates
