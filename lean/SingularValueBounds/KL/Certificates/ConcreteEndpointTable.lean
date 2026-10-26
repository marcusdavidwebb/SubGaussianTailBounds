import SingularValueBounds.KL.Lower.EndpointCertificates
import SingularValueBounds.KL.Certificates.TensorBernsteinIdentity

/-! Kernel-checked tensor coefficients for all eight endpoint lower-cost rectangles. -/
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private def endpointTableCoefficients00 (k : Fin 7) (l : Fin 5) : ℚ :=
  (![
    ![(858489265666197/320000000000000000), (-45699504752733/80000000000000000), (14254784790679/16000000000000000), (80723023241/2000000000000000), (3054635951/4000000000000000), (23301587/5000000000000000), (-31827/5000000000000000)],
    ![(1258605621/64000000000), (-60233229/32000000000), (383607/16000000000), (4473/8000000000), 0, 0, 0],
    ![(-167171372028801/10240000000000000), (1102058561793/1280000000000000), (30004654953/1280000000000000), (54012357/320000000000000), (281799/640000000000000), 0, 0],
    ![(11755571733927/2560000000000000), (-329560560623/1280000000000000), (-3700708291/640000000000000), (-8109549/320000000000000), 0, 0, 0],
    ![(-1090093686129/2560000000000000), (17036360327/640000000000000), (233374799/640000000000000), 0, 0, 0, 0]]) l k

private theorem endpointTableBox00 :
    BoxCertificate (endpointMarginPoly 0) 6 4 (endpointBox 0 0) := by
  refine ⟨by norm_num [endpointBox, endpointKLo, endpointKHi],
    by norm_num [endpointBox, Fin.val_natCast, Fin.coe_ofNat_eq_mod], ?_⟩
  have hpoly : tensorAffine (endpointMarginPoly 0)
      (endpointBox 0 0).left ((endpointBox 0 0).right-(endpointBox 0 0).left)
      (endpointBox 0 0).bottom ((endpointBox 0 0).top-(endpointBox 0 0).bottom) =
      tensorOfFn 6 4 endpointTableCoefficients00 := by
    apply tensor_eq_of_eval
    intro a b
    rw [tensorAffine_eval]
    simp only [tensorOfFn, Polynomial.ofFn_eq_sum_monomial,
      endpointMarginPoly, endpointOPoly, endpointNMajorantPoly, endpointGPoly,
      endpointNPoly, endpointAPoly, endpointC, endpointTheta, endpointXi,
      endpointChi, endpointOmega, Polynomial.eval₂_finset_sum,
      Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Polynomial.eval₂_monomial, Polynomial.coe_evalRingHom, Polynomial.eval_finset_sum,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_monomial]
    norm_num [endpointTableCoefficients00, endpointBox, endpointKLo, endpointKHi,
      Fin.sum_univ_succ, Fin.val_natCast, Fin.coe_ofNat_eq_mod, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
      Polynomial.eval₂_C, Polynomial.coe_evalRingHom]
    ring
  dsimp only
  rw [hpoly]
  constructor
  · exact tensorOfFn_bernstein_identity 6 4 endpointTableCoefficients00
  · simp_rw [tensorCoefficients_ofFn]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private def endpointTableCoefficients01 (k : Fin 7) (l : Fin 5) : ℚ :=
  (![
    ![(13042387002963663/1280000000000000000), (-145871907138733/80000000000000000), (29853533280583/32000000000000000), (82128165791/2000000000000000), (12225588779/16000000000000000), (23301587/5000000000000000), (-31827/5000000000000000)],
    ![(-4670241434271/5120000000000000), (-1057602835667/1280000000000000), (8795077319/160000000000000), (262616067/320000000000000), (281799/320000000000000), 0, 0],
    ![(-52266759688773/10240000000000000), (39726650481/160000000000000), (2120180559/256000000000000), (2968371/32000000000000), (281799/640000000000000), 0, 0],
    ![(7395196989411/2560000000000000), (-193269678007/1280000000000000), (-553441819/128000000000000), (-8109549/320000000000000), 0, 0, 0],
    ![(-1090093686129/2560000000000000), (17036360327/640000000000000), (233374799/640000000000000), 0, 0, 0, 0]]) l k

private theorem endpointTableBox01 :
    BoxCertificate (endpointMarginPoly 0) 6 4 (endpointBox 0 1) := by
  refine ⟨by norm_num [endpointBox, endpointKLo, endpointKHi],
    by norm_num [endpointBox, Fin.val_natCast, Fin.coe_ofNat_eq_mod], ?_⟩
  have hpoly : tensorAffine (endpointMarginPoly 0)
      (endpointBox 0 1).left ((endpointBox 0 1).right-(endpointBox 0 1).left)
      (endpointBox 0 1).bottom ((endpointBox 0 1).top-(endpointBox 0 1).bottom) =
      tensorOfFn 6 4 endpointTableCoefficients01 := by
    apply tensor_eq_of_eval
    intro a b
    rw [tensorAffine_eval]
    simp only [tensorOfFn, Polynomial.ofFn_eq_sum_monomial,
      endpointMarginPoly, endpointOPoly, endpointNMajorantPoly, endpointGPoly,
      endpointNPoly, endpointAPoly, endpointC, endpointTheta, endpointXi,
      endpointChi, endpointOmega, Polynomial.eval₂_finset_sum,
      Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Polynomial.eval₂_monomial, Polynomial.coe_evalRingHom, Polynomial.eval_finset_sum,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_monomial]
    norm_num [endpointTableCoefficients01, endpointBox, endpointKLo, endpointKHi,
      Fin.sum_univ_succ, Fin.val_natCast, Fin.coe_ofNat_eq_mod, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
      Polynomial.eval₂_C, Polynomial.coe_evalRingHom]
    ring
  dsimp only
  rw [hpoly]
  constructor
  · exact tensorOfFn_bernstein_identity 6 4 endpointTableCoefficients01
  · simp_rw [tensorCoefficients_ofFn]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private def endpointTableCoefficients02 (k : Fin 7) (l : Fin 5) : ℚ :=
  (![
    ![(66359635429221/10000000000000000), (-202058568961983/80000000000000000), (15875439799729/16000000000000000), (20976088679/500000000000000), (1530840463/2000000000000000), (23301587/5000000000000000), (-31827/5000000000000000)],
    ![(-2128656867561/512000000000000), (-54093411211/80000000000000), (19206541991/320000000000000), (7441371/8000000000000), (281799/160000000000000), 0, 0],
    ![(10313355717063/10240000000000000), (-57559506249/1280000000000000), (-3201854187/1280000000000000), (5355063/320000000000000), (281799/640000000000000), 0, 0],
    ![(606964448979/512000000000000), (-56978795391/1280000000000000), (-1833709899/640000000000000), (-8109549/320000000000000), 0, 0, 0],
    ![(-1090093686129/2560000000000000), (17036360327/640000000000000), (233374799/640000000000000), 0, 0, 0, 0]]) l k

private theorem endpointTableBox02 :
    BoxCertificate (endpointMarginPoly 0) 6 4 (endpointBox 0 2) := by
  refine ⟨by norm_num [endpointBox, endpointKLo, endpointKHi],
    by norm_num [endpointBox, Fin.val_natCast, Fin.coe_ofNat_eq_mod], ?_⟩
  have hpoly : tensorAffine (endpointMarginPoly 0)
      (endpointBox 0 2).left ((endpointBox 0 2).right-(endpointBox 0 2).left)
      (endpointBox 0 2).bottom ((endpointBox 0 2).top-(endpointBox 0 2).bottom) =
      tensorOfFn 6 4 endpointTableCoefficients02 := by
    apply tensor_eq_of_eval
    intro a b
    rw [tensorAffine_eval]
    simp only [tensorOfFn, Polynomial.ofFn_eq_sum_monomial,
      endpointMarginPoly, endpointOPoly, endpointNMajorantPoly, endpointGPoly,
      endpointNPoly, endpointAPoly, endpointC, endpointTheta, endpointXi,
      endpointChi, endpointOmega, Polynomial.eval₂_finset_sum,
      Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Polynomial.eval₂_monomial, Polynomial.coe_evalRingHom, Polynomial.eval_finset_sum,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_monomial]
    norm_num [endpointTableCoefficients02, endpointBox, endpointKLo, endpointKHi,
      Fin.sum_univ_succ, Fin.val_natCast, Fin.coe_ofNat_eq_mod, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
      Polynomial.eval₂_C, Polynomial.coe_evalRingHom]
    ring
  dsimp only
  rw [hpoly]
  constructor
  · exact tensorOfFn_bernstein_identity 6 4 endpointTableCoefficients02
  · simp_rw [tensorCoefficients_ofFn]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private def endpointTableCoefficients03 (k : Fin 7) (l : Fin 5) : ℚ :=
  (![
    ![(5433924910053663/1280000000000000000), (-8161908718269/2500000000000000), (33511470688883/32000000000000000), (171494963857/4000000000000000), (12281948579/16000000000000000), (23301587/5000000000000000), (-31827/5000000000000000)],
    ![(-1485028978209/5120000000000000), (-1015259095431/1280000000000000), (15321799647/320000000000000), (284036319/320000000000000), (845397/320000000000000), 0, 0],
    ![(20568974188707/10240000000000000), (-12029784249/640000000000000), (-11403615993/1280000000000000), (-1185849/20000000000000), (281799/640000000000000), 0, 0],
    ![(-1325552499621/2560000000000000), (3172483489/51200000000000), (-900210703/640000000000000), (-8109549/320000000000000), 0, 0, 0],
    ![(-1090093686129/2560000000000000), (17036360327/640000000000000), (233374799/640000000000000), 0, 0, 0, 0]]) l k

private theorem endpointTableBox03 :
    BoxCertificate (endpointMarginPoly 0) 6 4 (endpointBox 0 3) := by
  refine ⟨by norm_num [endpointBox, endpointKLo, endpointKHi],
    by norm_num [endpointBox, Fin.val_natCast, Fin.coe_ofNat_eq_mod], ?_⟩
  have hpoly : tensorAffine (endpointMarginPoly 0)
      (endpointBox 0 3).left ((endpointBox 0 3).right-(endpointBox 0 3).left)
      (endpointBox 0 3).bottom ((endpointBox 0 3).top-(endpointBox 0 3).bottom) =
      tensorOfFn 6 4 endpointTableCoefficients03 := by
    apply tensor_eq_of_eval
    intro a b
    rw [tensorAffine_eval]
    simp only [tensorOfFn, Polynomial.ofFn_eq_sum_monomial,
      endpointMarginPoly, endpointOPoly, endpointNMajorantPoly, endpointGPoly,
      endpointNPoly, endpointAPoly, endpointC, endpointTheta, endpointXi,
      endpointChi, endpointOmega, Polynomial.eval₂_finset_sum,
      Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Polynomial.eval₂_monomial, Polynomial.coe_evalRingHom, Polynomial.eval_finset_sum,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_monomial]
    norm_num [endpointTableCoefficients03, endpointBox, endpointKLo, endpointKHi,
      Fin.sum_univ_succ, Fin.val_natCast, Fin.coe_ofNat_eq_mod, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
      Polynomial.eval₂_C, Polynomial.coe_evalRingHom]
    ring
  dsimp only
  rw [hpoly]
  constructor
  · exact tensorOfFn_bernstein_identity 6 4 endpointTableCoefficients03
  · simp_rw [tensorCoefficients_ofFn]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private def endpointTableCoefficients10 (k : Fin 7) (l : Fin 5) : ℚ :=
  (![
    ![(57419581/38063308800), (72870749/3806330880), (9043874963/3083128012800), (31538527/210213273600), (93350203/27748152115200), (2729809/124866684518400), (-10609/83244456345600)],
    ![(454867/18022400), (-1361003/486604800), (-3437/486604800), (497/716636160), 0, 0, 0],
    ![(-76811202881/3806330880000), (5134597349/2854748160000), (2419846723/51385466880000), (336581/1401421824000), (3479/8255648563200), 0, 0],
    ![(8151680719/1585971200000), (-20108257351/42821222400000), (-1408299347/128463667200000), (-2216123/63063982080000), 0, 0, 0],
    ![(-9881692457/23789568000000), (1411670351/35684352000000), (1411670351/1926955008000000), 0, 0, 0, 0]]) l k

private theorem endpointTableBox10 :
    BoxCertificate (endpointMarginPoly 1) 6 4 (endpointBox 1 0) := by
  refine ⟨by norm_num [endpointBox, endpointKLo, endpointKHi],
    by norm_num [endpointBox, Fin.val_natCast, Fin.coe_ofNat_eq_mod], ?_⟩
  have hpoly : tensorAffine (endpointMarginPoly 1)
      (endpointBox 1 0).left ((endpointBox 1 0).right-(endpointBox 1 0).left)
      (endpointBox 1 0).bottom ((endpointBox 1 0).top-(endpointBox 1 0).bottom) =
      tensorOfFn 6 4 endpointTableCoefficients10 := by
    apply tensor_eq_of_eval
    intro a b
    rw [tensorAffine_eval]
    simp only [tensorOfFn, Polynomial.ofFn_eq_sum_monomial,
      endpointMarginPoly, endpointOPoly, endpointNMajorantPoly, endpointGPoly,
      endpointNPoly, endpointAPoly, endpointC, endpointTheta, endpointXi,
      endpointChi, endpointOmega, Polynomial.eval₂_finset_sum,
      Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Polynomial.eval₂_monomial, Polynomial.coe_evalRingHom, Polynomial.eval_finset_sum,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_monomial]
    norm_num [endpointTableCoefficients10, endpointBox, endpointKLo, endpointKHi,
      Fin.sum_univ_succ, Fin.val_natCast, Fin.coe_ofNat_eq_mod, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
      Polynomial.eval₂_C, Polynomial.coe_evalRingHom]
    ring
  dsimp only
  rw [hpoly]
  constructor
  · exact tensorOfFn_bernstein_identity 6 4 endpointTableCoefficients10
  · simp_rw [tensorCoefficients_ofFn]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private def endpointTableCoefficients11 (k : Fin 7) (l : Fin 5) : ℚ :=
  (![
    ![(358180237929/31719424000000), (39512102581/2230272000000), (11419685528267/3853910016000000), (48071839/318504960000), (3361028267/998933476147200), (2729809/124866684518400), (-10609/83244456345600)],
    ![(-21611155657/15859712000000), (-96395489491/214106112000000), (55075597507/963477504000000), (67379921/63063982080000), (3479/4127824281600), 0, 0],
    ![(-690138161573/95158272000000), (7460615197/11894784000000), (2654874341/142737408000000), (177037/1313832960000), (3479/8255648563200), 0, 0],
    ![(82748440957/23789568000000), (-66661198331/214106112000000), (-15477808801/1926955008000000), (-2216123/63063982080000), 0, 0, 0],
    ![(-9881692457/23789568000000), (1411670351/35684352000000), (1411670351/1926955008000000), 0, 0, 0, 0]]) l k

private theorem endpointTableBox11 :
    BoxCertificate (endpointMarginPoly 1) 6 4 (endpointBox 1 1) := by
  refine ⟨by norm_num [endpointBox, endpointKLo, endpointKHi],
    by norm_num [endpointBox, Fin.val_natCast, Fin.coe_ofNat_eq_mod], ?_⟩
  have hpoly : tensorAffine (endpointMarginPoly 1)
      (endpointBox 1 1).left ((endpointBox 1 1).right-(endpointBox 1 1).left)
      (endpointBox 1 1).bottom ((endpointBox 1 1).top-(endpointBox 1 1).bottom) =
      tensorOfFn 6 4 endpointTableCoefficients11 := by
    apply tensor_eq_of_eval
    intro a b
    rw [tensorAffine_eval]
    simp only [tensorOfFn, Polynomial.ofFn_eq_sum_monomial,
      endpointMarginPoly, endpointOPoly, endpointNMajorantPoly, endpointGPoly,
      endpointNPoly, endpointAPoly, endpointC, endpointTheta, endpointXi,
      endpointChi, endpointOmega, Polynomial.eval₂_finset_sum,
      Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Polynomial.eval₂_monomial, Polynomial.coe_evalRingHom, Polynomial.eval_finset_sum,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_monomial]
    norm_num [endpointTableCoefficients11, endpointBox, endpointKLo, endpointKHi,
      Fin.sum_univ_succ, Fin.val_natCast, Fin.coe_ofNat_eq_mod, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
      Polynomial.eval₂_C, Polynomial.coe_evalRingHom]
    ring
  dsimp only
  rw [hpoly]
  constructor
  · exact tensorOfFn_bernstein_identity 6 4 endpointTableCoefficients11
  · simp_rw [tensorCoefficients_ofFn]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private def endpointTableCoefficients12 (k : Fin 7) (l : Fin 5) : ℚ :=
  (![
    ![(11379221089/1982464000000), (209603680867/11894784000000), (5841768624301/1926955008000000), (24978869/164229120000), (420286393/124866684518400), (2729809/124866684518400), (-10609/83244456345600)],
    ![(-56255753743/7929856000000), (760393879/26763264000000), (70523028611/963477504000000), (607243/492687360000), (3479/2063912140800), 0, 0],
    ![(65682510943/95158272000000), (-4957462937/71368704000000), (-157229681/142737408000000), (616469/21021327360000), (3479/8255648563200), 0, 0],
    ![(43221671129/23789568000000), (-32781109907/214106112000000), (-9831127397/1926955008000000), (-2216123/63063982080000), 0, 0, 0],
    ![(-9881692457/23789568000000), (1411670351/35684352000000), (1411670351/1926955008000000), 0, 0, 0, 0]]) l k

private theorem endpointTableBox12 :
    BoxCertificate (endpointMarginPoly 1) 6 4 (endpointBox 1 2) := by
  refine ⟨by norm_num [endpointBox, endpointKLo, endpointKHi],
    by norm_num [endpointBox, Fin.val_natCast, Fin.coe_ofNat_eq_mod], ?_⟩
  have hpoly : tensorAffine (endpointMarginPoly 1)
      (endpointBox 1 2).left ((endpointBox 1 2).right-(endpointBox 1 2).left)
      (endpointBox 1 2).bottom ((endpointBox 1 2).top-(endpointBox 1 2).bottom) =
      tensorOfFn 6 4 endpointTableCoefficients12 := by
    apply tensor_eq_of_eval
    intro a b
    rw [tensorAffine_eval]
    simp only [tensorOfFn, Polynomial.ofFn_eq_sum_monomial,
      endpointMarginPoly, endpointOPoly, endpointNMajorantPoly, endpointGPoly,
      endpointNPoly, endpointAPoly, endpointC, endpointTheta, endpointXi,
      endpointChi, endpointOmega, Polynomial.eval₂_finset_sum,
      Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Polynomial.eval₂_monomial, Polynomial.coe_evalRingHom, Polynomial.eval_finset_sum,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_monomial]
    norm_num [endpointTableCoefficients12, endpointBox, endpointKLo, endpointKHi,
      Fin.sum_univ_succ, Fin.val_natCast, Fin.coe_ofNat_eq_mod, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
      Polynomial.eval₂_C, Polynomial.coe_evalRingHom]
    ring
  dsimp only
  rw [hpoly]
  constructor
  · exact tensorOfFn_bernstein_identity 6 4 endpointTableCoefficients12
  · simp_rw [tensorCoefficients_ofFn]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private def endpointTableCoefficients13 (k : Fin 7) (l : Fin 5) : ℚ :=
  (![
    ![(70175992987/95158272000000), (623294321671/35684352000000), (11944545247567/3853910016000000), (268590169/1751777280000), (124607257/36997536153600), (2729809/124866684518400), (-10609/83244456345600)],
    ![(-30525174799/15859712000000), (-88124867887/214106112000000), (522935903/8921088000000), (6797959/5733089280000), (3479/1375941427200), 0, 0],
    ![(347181945523/95158272000000), (-2599816079/8921088000000), (-15430640519/1284636672000000), (-266609/3503554560000), (3479/8255648563200), 0, 0],
    ![(1231633767/7929856000000), (1098978517/214106112000000), (-1394815331/642318336000000), (-2216123/63063982080000), 0, 0, 0],
    ![(-9881692457/23789568000000), (1411670351/35684352000000), (1411670351/1926955008000000), 0, 0, 0, 0]]) l k

private theorem endpointTableBox13 :
    BoxCertificate (endpointMarginPoly 1) 6 4 (endpointBox 1 3) := by
  refine ⟨by norm_num [endpointBox, endpointKLo, endpointKHi],
    by norm_num [endpointBox, Fin.val_natCast, Fin.coe_ofNat_eq_mod], ?_⟩
  have hpoly : tensorAffine (endpointMarginPoly 1)
      (endpointBox 1 3).left ((endpointBox 1 3).right-(endpointBox 1 3).left)
      (endpointBox 1 3).bottom ((endpointBox 1 3).top-(endpointBox 1 3).bottom) =
      tensorOfFn 6 4 endpointTableCoefficients13 := by
    apply tensor_eq_of_eval
    intro a b
    rw [tensorAffine_eval]
    simp only [tensorOfFn, Polynomial.ofFn_eq_sum_monomial,
      endpointMarginPoly, endpointOPoly, endpointNMajorantPoly, endpointGPoly,
      endpointNPoly, endpointAPoly, endpointC, endpointTheta, endpointXi,
      endpointChi, endpointOmega, Polynomial.eval₂_finset_sum,
      Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Polynomial.eval₂_monomial, Polynomial.coe_evalRingHom, Polynomial.eval_finset_sum,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_monomial]
    norm_num [endpointTableCoefficients13, endpointBox, endpointKLo, endpointKHi,
      Fin.sum_univ_succ, Fin.val_natCast, Fin.coe_ofNat_eq_mod, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
      Polynomial.eval₂_C, Polynomial.coe_evalRingHom]
    ring
  dsimp only
  rw [hpoly]
  constructor
  · exact tensorOfFn_bernstein_identity 6 4 endpointTableCoefficients13
  · simp_rw [tensorCoefficients_ofFn]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

/-- Every endpoint lower-cost rectangle has its complete finite Lean certificate. -/
theorem endpointTableConditions : EndpointTableConditions := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact endpointTableBox00
  · exact endpointTableBox01
  · exact endpointTableBox02
  · exact endpointTableBox03
  · exact endpointTableBox10
  · exact endpointTableBox11
  · exact endpointTableBox12
  · exact endpointTableBox13

end SingularValueBounds.KL.Certificates
