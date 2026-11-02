import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block00
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block01
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block02
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block03
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block04
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block05
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block06
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block07
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block08
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block09
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block10
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block11
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block12
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block13
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block14
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block15
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block16
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block17
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block18
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block19
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block20
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block21
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block22
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block23
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block24
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block25
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block26
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block27
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block28
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block29
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block30
import SingularValueBounds.KL.Certificates.GeneralMeanCriticalLogs.Block31

/-! Shared exact upper logarithms for repeated general critical-point arguments.

Every proposed entry is checked by Lean once. Missing keys fall back to the
unchanged exact rounded evaluator, so this lookup adds no numerical premise and
preserves every original critical-margin obligation. The finite data are split
into bounded independent proofs; this root assembles their checked validities.
-/
namespace SingularValueBounds.KL.Certificates.GeneralCriticalLogs
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def cache : RoundedLogCache :=
(.node (1269/160) 2070810652480602 (.node (1309/250) 1655557848047695 (.node (15477/4000) 1353060689810756 (.node (12427/4000) 1133577163703994 (.node (531/200) 976444654693932 Block00.tree Block01.tree) (.node (6987/2000) 1250904099010395 Block02.tree Block03.tree)) (.node (4559/1000) 1517103301231347 (.node (3377/800) 1440131292717683 Block04.tree Block05.tree) (.node (979/200) 1588214275982516 Block06.tree Block07.tree))) (.node (13137/2000) 1882285495927465 (.node (5901/1000) 1775121828075073 (.node (11139/2000) 1717305283303148 Block08.tree Block09.tree) (.node (24947/4000) 1830459213367247 Block10.tree Block11.tree)) (.node (14491/2000) 1980380586503880 (.node (27621/4000) 1932281991853967 Block12.tree Block13.tree) (.node (7587/1000) 2026436256355978 Block14.tree Block15.tree)))) (.node (44979/4000) 2419901353061039 (.node (37797/4000) 2245935373276765 (.node (1083/125) 2159176509698746 (.node (6631/800) 2114899173700996 Block16.tree Block17.tree) (.node (3619/400) 2202488476455816 Block18.tree Block19.tree)) (.node (10293/1000) 2331464052544476 (.node (39437/4000) 2288410100812794 Block20.tree Block21.tree) (.node (42993/4000) 2374742950624207 Block22.tree Block23.tree))) (.node (55107/4000) 2622982388712196 (.node (989/80) 2514667696948883 (.node (1472/125) 2466063561986574 Block24.tree Block25.tree) (.node (52007/4000) 2565083963786366 Block26.tree Block27.tree)) (.node (255/16) 2768674822918695 (.node (29463/2000) 2689988058283854 Block28.tree Block29.tree) (.node (35391/2000) 2873310369967939 Block30.tree Block31.tree)))))

theorem valid : cache.valid true = true := by
  unfold cache
  refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
  · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
    · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
      · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
        · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
          · exact Block00.valid
          · exact Block01.valid
        · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
          · exact Block02.valid
          · exact Block03.valid
      · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
        · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
          · exact Block04.valid
          · exact Block05.valid
        · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
          · exact Block06.valid
          · exact Block07.valid
    · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
      · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
        · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
          · exact Block08.valid
          · exact Block09.valid
        · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
          · exact Block10.valid
          · exact Block11.valid
      · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
        · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
          · exact Block12.valid
          · exact Block13.valid
        · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
          · exact Block14.valid
          · exact Block15.valid
  · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
    · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
      · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
        · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
          · exact Block16.valid
          · exact Block17.valid
        · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
          · exact Block18.valid
          · exact Block19.valid
      · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
        · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
          · exact Block20.valid
          · exact Block21.valid
        · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
          · exact Block22.valid
          · exact Block23.valid
    · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
      · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
        · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
          · exact Block24.valid
          · exact Block25.valid
        · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
          · exact Block26.valid
          · exact Block27.valid
      · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
        · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
          · exact Block28.valid
          · exact Block29.valid
        · refine RoundedLogCache.node_valid true _ _ _ _ (by decide +kernel) ?_ ?_
          · exact Block30.valid
          · exact Block31.valid

/-- The checked shared values preserve the original upper rounded logarithm. -/
theorem upper_eq_cache (x : ℚ) :
    (logRoundedQ x).2 = cache.get true x :=
  roundedLog_upper_eq_cache cache valid x

end SingularValueBounds.KL.Certificates.GeneralCriticalLogs
