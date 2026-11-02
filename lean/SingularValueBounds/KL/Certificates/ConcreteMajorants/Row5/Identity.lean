import SingularValueBounds.KL.Certificates.ConcreteUpperPolynomials
import SingularValueBounds.KL.Certificates.TensorBernsteinIdentity

/-! Shared exact polynomial identity for determinant majorant 5. -/
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates.MajorantRow5
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
noncomputable def baseCoefficients : Fin 9 → Fin 14 → ℚ :=
  fun k l => (![![(3102951/8000000), (-2879237/1000000), (548663/50000), (-12199/2500), (18903/250), (0/1), (0/1), (0/1), (0/1)],
      ![(-26486393/8400000), (51228857/3500000), (-12334153/175000), (-466421/8750), (-302448/875), (0/1), (0/1), (0/1), (0/1)],
      ![(136167863/10500000), (-12690103/350000), (39219027/218750), (5731934/21875), (2365952/4375), (-302448/875), (0/1), (0/1), (0/1)],
      ![(-35045981/2187500), (906052127/26250000), (-27170489/218750), (-6603634/21875), (3034152/4375), (907344/875), (0/1), (0/1), (0/1)],
      ![(-1110670151/52500000), (11372079/437500), (-5556589751/17500000), (-912809837/1312500), (-64477587/21875), (-3775764/4375), (453672/875), (0/1), (0/1)],
      ![(53915993/625000), (-335804191/2187500), (3304561863/4375000), (6304334167/3281250), (257460118/109375), (-52513416/21875), (-3629376/4375), (0/1), (0/1)],
      ![(-41628849/875000), (90060899/546875), (-2856646427/8750000), (-1839676373/2187500), (6196546592/1640625), (447818816/109375), (4927088/21875), (-1209792/4375), (0/1)],
      ![(-41927891/468750), (47293971/2187500), (-1512937889/2187500), (-34119851099/13125000), (-3510223797/546875), (-114807428/109375), (42147536/21875), (604896/4375), (0/1)],
      ![(961374383/6562500), (-153694272/546875), (82931803/87500), (3416427403/1093750), (23068083111/17500000), (-10853166437/2187500), (-105308137/109375), (-48796/21875), (151224/4375)],
      ![(5925739/546875), (487328959/3281250), (-59993081/546875), (199711369/2187500), (24711274671/4375000), (536175251/218750), (26742/3125), (-1361016/4375), (0/1)],
      ![(-140550157/1640625), (9213402/109375), (-1331368747/2187500), (-1414412701/546875), (-291469924/109375), (454288/21875), (4839168/4375), (0/1), (0/1)],
      ![(29706884/546875), (-62899671/546875), (153292933/546875), (109991492/109375), (-3314704/21875), (-1209792/625), (0/1), (0/1), (0/1)],
      ![(2728993/156250), (18189936/546875), (2752/15625), (5720832/21875), (7258752/4375), (0/1), (0/1), (0/1), (0/1)],
      ![(-10853442/546875), (4379672/109375), (-3250784/21875), (-2419584/4375), (0/1), (0/1), (0/1), (0/1), (0/1)]]) l k
theorem quotient_identity : majorantQuotient 5 = tensorOfFn 8 13 baseCoefficients := by
  apply mul_left_cancel₀ (pow_ne_zero 2 (Polynomial.X_ne_zero : (X : Polynomial (Polynomial ℚ)) ≠ 0))
  rw [← majorant_cleared_factorization]
  apply tensor_eq_of_eval
  intro a b
  simp [majorantCleared, majorantHQ, majorantAQ, majorantBQ, padeDQ, padeNQ,
    comparisonZQ, tensorOfFn, baseCoefficients, Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_succ, Polynomial.eval₂_monomial,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_monomial]
  ring

end SingularValueBounds.KL.Certificates.MajorantRow5
