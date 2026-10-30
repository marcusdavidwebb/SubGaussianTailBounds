import SingularValueBounds.KL.Upper.CertificateData
import SingularValueBounds.KL.Certificates.AffineCoefficientIdentity

/-! Exact upper-rate polynomial leaf certificates.
The unshifted polynomial identity is shared across leaves. Each affine transform
and every Bernstein coefficient sign is checked by Lean's kernel. -/
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The unshifted coefficient vector is shared by every subdivision leaf. -/
private noncomputable def rateBase12 : Fin 28 → ℚ := ![(226492416/125),
    (2434793472/125),
    (7198998528/125),
    (2049835008/125),
    (-49446125568/125),
    (-176816111616/125),
    (-306050420736/125),
    (-1108109048832/875),
    (4991784756864/875),
    (18669993949536/875),
    (1125735290712/25),
    (688078643978718/9625),
    (891164569789881/9625),
    (2537869429464669/25025),
    (4792905446998671/50050),
    (758564903726919/9625),
    (1094700278778201/19250),
    (31554719640027/875),
    (2511134513406/125),
    (8574064605828/875),
    (3639564793968/875),
    (38042359968/25),
    (59108878656/125),
    (15269369472/125),
    (3171788928/125),
    (4011264/1),
    (54326784/125),
    (3099648/125)]

private theorem ratePolynomial_identity12 : ratePolynomial (3/1) (27/2000) = Polynomial.ofFn 28 rateBase12 := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  apply Polynomial.funext
  intro x
  simp [rateBase12, ratePolynomial, Finset.sum_range_succ, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Fin.sum_univ_succ, Polynomial.eval_finset_sum, Polynomial.eval_monomial]
  ring

private theorem rate_12_leaf_0 :
    IntervalCertificate (ratePolynomial (3/1) (27/2000)) (0/1) (1/4) 27
      (bernsteinCoefficients ((ratePolynomial (3/1) (27/2000)).comp
        (affine (0/1) ((1/4)-(0/1)))) 27) := by
  refine Or.inr ⟨by norm_num, ?_⟩
  let coefficients : Fin 28 → ℚ := ![(226492416/125),
      (608698368/125),
      (449937408/125),
      (32028672/125),
      (-193148928/125),
      (-172671984/125),
      (-74719341/125),
      (-1082137743/14000),
      (38998318413/448000),
      (583437310923/7168000),
      (140716911339/3276800),
      (344039321989359/20185088000),
      (891164569789881/161480704000),
      (2537869429464669/1679399321600),
      (4792905446998671/13435194572800),
      (758564903726919/10334765056000),
      (1094700278778201/82678120448000),
      (31554719640027/15032385536000),
      (1255567256703/4294967296000),
      (2143516151457/60129542144000),
      (227472799623/60129542144000),
      (1188823749/3435973836800),
      (923576229/34359738368000),
      (119291949/68719476736000),
      (24779601/274877906944000),
      (15669/4398046511104),
      (106107/1099511627776000),
      (3027/2199023255552000)]
  have hpoly : (ratePolynomial (3/1) (27/2000)).comp
      (affine (0/1) ((1/4)-(0/1))) = Polynomial.ofFn 28 coefficients := by
    rw [ratePolynomial_identity12]
    apply ofFn_comp_affine_eq 27
    simp only [Nat.choose_eq_fast_choose]
    decide +kernel
  rw [hpoly]
  constructor
  · apply polynomial_bernstein_identity
    exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by norm_num) coefficients)
  · simp_rw [bernsteinCoefficients_ofFn]
    simp only [Nat.choose_eq_fast_choose]
    decide +kernel

private theorem rate_12_leaf_1 :
    IntervalCertificate (ratePolynomial (3/1) (27/2000)) (1/4) (1/2) 27
      (bernsteinCoefficients ((ratePolynomial (3/1) (27/2000)).comp
        (affine (1/4) ((1/2)-(1/4)))) 27) := by
  refine Or.inr ⟨by norm_num, ?_⟩
  let coefficients : Fin 28 → ℚ := ![(57404236522079156075631/8004444650209280),
      (-986094101806286112358443/440244455761510400),
      (-3478702384476486322487793/169324790677504000),
      (-62420857238306770984359/4837851162214400),
      (1284149197900553236427223/84662395338752000),
      (2925907793354017808311851/84662395338752000),
      (263977125774041549664063/7696581394432000),
      (25499334368597117549373/1099511627776000),
      (5287374484101682009083/439804651110400),
      (77661428647252977599949/15393162788864000),
      (27217541716140552571143/15393162788864000),
      (8124121742129378902179/15393162788864000),
      (1150838910828294291897/8466239533875200),
      (3354033631172897301441/110061113940377600),
      (3290896050978483152979/550305569701888000),
      (43619671628311443051/42331197669376000),
      (3775231485962648241/24189255811072000),
      (12781798908198297/615726511554560),
      (297721231662567/123145302310912),
      (3775375562908311/15393162788864000),
      (165500013476061/7696581394432000),
      (1771111666239/1099511627776000),
      (111528715569/1099511627776000),
      (1153025601/219902325555200),
      (471922833/2199023255552000),
      (14414541/2199023255552000),
      (293943/2199023255552000),
      (3027/2199023255552000)]
  have hpoly : (ratePolynomial (3/1) (27/2000)).comp
      (affine (1/4) ((1/2)-(1/4))) = Polynomial.ofFn 28 coefficients := by
    rw [ratePolynomial_identity12]
    apply ofFn_comp_affine_eq 27
    simp only [Nat.choose_eq_fast_choose]
    decide +kernel
  rw [hpoly]
  constructor
  · apply polynomial_bernstein_identity
    exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by norm_num) coefficients)
  · simp_rw [bernsteinCoefficients_ofFn]
    simp only [Nat.choose_eq_fast_choose]
    decide +kernel

private theorem rate_12_leaf_2 :
    IntervalCertificate (ratePolynomial (3/1) (27/2000)) (1/2) (1/1) 27
      (bernsteinCoefficients ((ratePolynomial (3/1) (27/2000)).comp
        (affine (1/2) ((1/1)-(1/2)))) 27) := by
  refine Or.inr ⟨by norm_num, ?_⟩
  let coefficients : Fin 28 → ℚ := ![(5034835959253479/51251200),
      (21998350977285609/16016000),
      (79546060566417843/9856000),
      (65615209646596083/2464000),
      (1146030058332005697/19712000),
      (8133982630078707/88000),
      (50886171687493143/448000),
      (3591074980416609/32000),
      (16414866391190661/179200),
      (18058339751358231/286720),
      (30306352221374499/819200),
      (23660510704491168747/1261568000),
      (1303561667570038893/157696000),
      (13052905094803982217/4100096000),
      (550751031838907547/512512000),
      (50202040580542839/157696000),
      (1863974495183973/22528000),
      (539861596143339/28672000),
      (10715301302163/2867200),
      (1475108353233/2293760),
      (272712367341/2867200),
      (48923394291/4096000),
      (640914339/512000),
      (54683871/512000),
      (14635497/2048000),
      (1444971/4096000),
      (46959/4096000),
      (3027/16384000)]
  have hpoly : (ratePolynomial (3/1) (27/2000)).comp
      (affine (1/2) ((1/1)-(1/2))) = Polynomial.ofFn 28 coefficients := by
    rw [ratePolynomial_identity12]
    apply ofFn_comp_affine_eq 27
    simp only [Nat.choose_eq_fast_choose]
    decide +kernel
  rw [hpoly]
  constructor
  · apply polynomial_bernstein_identity
    exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by norm_num) coefficients)
  · simp_rw [bernsteinCoefficients_ofFn]
    simp only [Nat.choose_eq_fast_choose]
    decide +kernel

private theorem rate_12_leaf_3 :
    IntervalCertificate (ratePolynomial (3/1) (27/2000)) (1/1) (2/1) 27
      (bernsteinCoefficients ((ratePolynomial (3/1) (27/2000)).comp
        (affine (1/1) ((2/1)-(1/1)))) 27) := by
  refine Or.inr ⟨by norm_num, ?_⟩
  let coefficients : Fin 28 → ℚ := ![(79558333606944774/125125),
      (215075141697987234/25025),
      (1069400407778752779/19250),
      (200655707987220957/875),
      (13104133301332680813/19250),
      (14923896499930869999/9625),
      (197552285217888129/70),
      (3691576169065173051/875),
      (9243161094081662019/1750),
      (4914369398565111879/875),
      (8969848034274259047/1750),
      (7786952045571057921/1925),
      (7632934399105137249/2750),
      (41582997160385613441/25025),
      (565225654664445357/650),
      (547175940756414177/1375),
      (87491130508480389/550),
      (48469769906945451/875),
      (14637502248142686/875),
      (3808257065495172/875),
      (33827937363216/35),
      (4521482450592/25),
      (700275304896/25),
      (437463164544/125),
      (42429664128/125),
      (3001880832/125),
      (27603456/25),
      (3099648/125)]
  have hpoly : (ratePolynomial (3/1) (27/2000)).comp
      (affine (1/1) ((2/1)-(1/1))) = Polynomial.ofFn 28 coefficients := by
    rw [ratePolynomial_identity12]
    apply ofFn_comp_affine_eq 27
    simp only [Nat.choose_eq_fast_choose]
    decide +kernel
  rw [hpoly]
  constructor
  · apply polynomial_bernstein_identity
    exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by norm_num) coefficients)
  · simp_rw [bernsteinCoefficients_ofFn]
    simp only [Nat.choose_eq_fast_choose]
    decide +kernel

theorem concrete_rate_row_12 :
    ∀ cell ∈ (rateTrees 12).leaves 0 ((rateRows 12).1-1),
      IntervalCertificate (ratePolynomial (rateRows 12).1 (rateRows 12).2)
        cell.1 cell.2 27
        (bernsteinCoefficients ((ratePolynomial (rateRows 12).1 (rateRows 12).2).comp
          (affine cell.1 (cell.2-cell.1))) 27) := by
  intro cell hc
  have hrow : rateRows 12 = ((3/1), (27/2000)) := by rfl
  rw [hrow] at hc ⊢
  have hleaves : (rateTrees 12).leaves 0 ((3/1)-1) =
      [((0/1), (1/4)), ((1/4), (1/2)), ((1/2), (1/1)), ((1/1), (2/1))] := by decide +kernel
  rw [hleaves] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact rate_12_leaf_0
  · exact rate_12_leaf_1
  · exact rate_12_leaf_2
  · exact rate_12_leaf_3

end SingularValueBounds.KL.Certificates
