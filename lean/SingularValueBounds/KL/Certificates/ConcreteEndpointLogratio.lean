import SingularValueBounds.KL.Upper.EndpointLogratio
import SingularValueBounds.KL.Certificates.TensorBernsteinIdentity

/-! Concrete kernel-checked endpoint logarithmic-ratio tensor certificate. -/
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL
open Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private def endpointLogratioCoefficients (k : Fin 7) (l : Fin 19) : ℚ :=
  (![
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0],
    ![(40131/125000), (3087/25000), 0, 0, 0, 0, 0],
    ![(-3769227/5000000), (-225351/2500000), (21609/1000000), 0, 0, 0, 0],
    ![(333145953/781250000), (-34812099/125000000), (-64827/1000000), 0, 0, 0, 0],
    ![(209478531969/625000000000), (49979866671/125000000000), (26773551/5000000000), (-6201783/1000000000), 0, 0, 0],
    ![(-295699349547/625000000000), (-4964905449/78125000000), (45065331801/625000000000), (92119167/12500000000), 0, 0, 0],
    ![(21851139714327/250000000000000), (-2175381422613/12500000000000), (-1225340570727/25000000000000), (30662976519/12500000000000), (1045076067/2000000000000), 0, 0],
    ![(30996118603989/250000000000000), (80782156413/781250000000), (-944637586263/125000000000000), (-161719962453/31250000000000), (-36888961599/250000000000000), 0, 0],
    ![(-687244000633029/10000000000000000), (15993466123131/2000000000000000), (87262939932399/5000000000000000), (7638816744279/5000000000000000), (-1042696851273/10000000000000000), (-22880495169/2000000000000000), 0],
    ![(-801038509034967/250000000000000000), (-122006427072831/5000000000000000), (-120740373006813/25000000000000000), (3821042693223/6250000000000000), (5788765277757/50000000000000000), (-205924456521/125000000000000000), 0],
    ![(303402992772663/25000000000000000), (764139897159093/125000000000000000), (-176339976267483/125000000000000000), (-58779992089161/125000000000000000), 0, 0, 0],
    ![(-67951432653198129/25000000000000000000), (7488122534453799/5000000000000000000), (2308436038095579/2500000000000000000), (70632088586703/2500000000000000000), (-10090298369529/5000000000000000000), (-10090298369529/25000000000000000000), 0],
    ![(-15217291085513013/25000000000000000000), (-2723259415509549/3125000000000000000), (-918217151627139/12500000000000000000), (70632088586703/6250000000000000000), (70632088586703/25000000000000000000), 0, 0],
    ![(19831920873177609/62500000000000000000), (4449821580962289/62500000000000000000), (-1483273860320763/62500000000000000000), (-494424620106921/62500000000000000000), 0, 0, 0],
    ![(-38070695748232917/1562500000000000000000), (3460972340748447/156250000000000000000), (3460972340748447/312500000000000000000), 0, 0, 0, 0],
    ![(-24226806385239129/3125000000000000000000), (-24226806385239129/3125000000000000000000), 0, 0, 0, 0, 0],
    ![(169587644696673903/78125000000000000000000), 0, 0, 0, 0, 0, 0]]) l k

/-- The complete logarithmic-ratio certificate has no remaining numerical premise. -/
theorem endpointLogratioCertificateConditions : EndpointLogratioCertificateConditions := by
  change BoxCertificate endpointLogratioCleared 6 18 endpointLogratioBox
  refine ⟨by norm_num [endpointLogratioBox], by norm_num [endpointLogratioBox], ?_⟩
  have hpoly : tensorAffine endpointLogratioCleared
      endpointLogratioBox.left (endpointLogratioBox.right-endpointLogratioBox.left)
      endpointLogratioBox.bottom (endpointLogratioBox.top-endpointLogratioBox.bottom) =
      tensorOfFn 6 18 endpointLogratioCoefficients := by
    apply tensor_eq_of_eval
    intro a b
    rw [tensorAffine_eval]
    simp only [tensorOfFn, Polynomial.ofFn_eq_sum_monomial,
      endpointLogratioCleared, endpointLogratioZQ, endpointLogratioZDerivativeQ,
      padeDQ, padeNQ, Polynomial.eval₂_finset_sum,
      Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Polynomial.eval₂_monomial, Polynomial.coe_evalRingHom, Polynomial.eval_finset_sum,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_monomial]
    norm_num [endpointLogratioCoefficients, endpointLogratioBox,
      Fin.sum_univ_succ, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
      Polynomial.eval₂_C, Polynomial.coe_evalRingHom]
    ring
  dsimp only
  rw [hpoly]
  constructor
  · exact tensorOfFn_bernstein_identity 6 18 endpointLogratioCoefficients
  · simp_rw [tensorCoefficients_ofFn]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

end SingularValueBounds.KL
