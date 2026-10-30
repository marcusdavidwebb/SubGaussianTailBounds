import SingularValueBounds.KL.Upper.GeneralMeanCellData
import SingularValueBounds.KL.Certificates.IntegerRoundedLogEvaluation

/-! The complete finite prefactor domains, checked in bounded batches. -/
namespace SingularValueBounds.KL.Certificates
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem prefactorDomainBlock0 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 0 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock1 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 1 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock2 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 2 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock3 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 3 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock4 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 4 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock5 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 5 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock6 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 6 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock7 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 7 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock8 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 8 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock9 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 9 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock10 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 10 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock11 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 11 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock12 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 12 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock13 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 13 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock14 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 14 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock15 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 15 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock16 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 16 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock17 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 17 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

private theorem prefactorDomainBlock18 (i : Fin 70) :
    roundUpQ (generalMeanRowBlocks 18 i).prefactorArgument < 82 := by
  revert i
  simp only [GeneralMeanRow.prefactorArgument, logRoundedQ_eq_integer]
  decide +kernel

theorem generalMeanRows_prefactorDomain (i : Fin 1330) :
    roundUpQ (generalMeanRows i).prefactorArgument < 82 := by
  have hall (b : Fin 19) (j : Fin 70) :
      roundUpQ (generalMeanRowBlocks b j).prefactorArgument < 82 := by
    fin_cases b
    · exact prefactorDomainBlock0 j
    · exact prefactorDomainBlock1 j
    · exact prefactorDomainBlock2 j
    · exact prefactorDomainBlock3 j
    · exact prefactorDomainBlock4 j
    · exact prefactorDomainBlock5 j
    · exact prefactorDomainBlock6 j
    · exact prefactorDomainBlock7 j
    · exact prefactorDomainBlock8 j
    · exact prefactorDomainBlock9 j
    · exact prefactorDomainBlock10 j
    · exact prefactorDomainBlock11 j
    · exact prefactorDomainBlock12 j
    · exact prefactorDomainBlock13 j
    · exact prefactorDomainBlock14 j
    · exact prefactorDomainBlock15 j
    · exact prefactorDomainBlock16 j
    · exact prefactorDomainBlock17 j
    · exact prefactorDomainBlock18 j
  exact hall ⟨i.val/70,by omega⟩ ⟨i.val%70,Nat.mod_lt _ (by norm_num)⟩

end SingularValueBounds.KL.Certificates
