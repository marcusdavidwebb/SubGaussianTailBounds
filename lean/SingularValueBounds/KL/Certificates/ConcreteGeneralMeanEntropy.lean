import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block00
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block01
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block02
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block03
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block04
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block05
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block06
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block07
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block08
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block09
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block10
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block11
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block12
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block13
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block14
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block15
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block16
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block17
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanEntropyRows.Block18
import SingularValueBounds.KL.Upper.GeneralMean
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanSmall

/-! Complete kernel-checked entropy conditions for all 1330 general rows and the small range. -/
namespace SingularValueBounds.KL.Certificates

theorem generalMeanEntropyConditions : SingularValueBounds.KL.GeneralMeanEntropyConditions := by
  constructor
  · intro i
    have hall (b : Fin 19) (j : Fin 70) : GeneralMeanNumericalConditions (generalMeanRowBlocks b j) := by
      fin_cases b
      · exact generalMeanEntropyBlock00 j
      · exact generalMeanEntropyBlock01 j
      · exact generalMeanEntropyBlock02 j
      · exact generalMeanEntropyBlock03 j
      · exact generalMeanEntropyBlock04 j
      · exact generalMeanEntropyBlock05 j
      · exact generalMeanEntropyBlock06 j
      · exact generalMeanEntropyBlock07 j
      · exact generalMeanEntropyBlock08 j
      · exact generalMeanEntropyBlock09 j
      · exact generalMeanEntropyBlock10 j
      · exact generalMeanEntropyBlock11 j
      · exact generalMeanEntropyBlock12 j
      · exact generalMeanEntropyBlock13 j
      · exact generalMeanEntropyBlock14 j
      · exact generalMeanEntropyBlock15 j
      · exact generalMeanEntropyBlock16 j
      · exact generalMeanEntropyBlock17 j
      · exact generalMeanEntropyBlock18 j
    exact hall ⟨i.val/70,by omega⟩ ⟨i.val%70,Nat.mod_lt _ (by norm_num)⟩
  · exact generalMeanSmallRow_numerical

end SingularValueBounds.KL.Certificates
