import SingularValueBounds.KL.Upper.GeneralMeanCells
import SingularValueBounds.KL.Certificates.TensorAffineIdentity
/-! Polynomial coefficient vectors for the existing general-mean determinant bounds.
Each displayed vector is proved equal to its defining polynomial in Lean. -/
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def generalMeanCoefficients0 (J : ℚ) : Fin 7 → Fin 16 → ℚ :=
  fun k l => (![![((-13/6) + J*(1/1)), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![((208/21) + J*(-32/7)), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![((-617/42) + J*(48/7)), ((187/21) + J*(-32/7)), (9/1), (0/1), (0/1), (0/1), (0/1)],
    ![((-431/35) + J*(192/35)), ((-267/7) + J*(96/7)), (-288/7), (0/1), (0/1), (0/1), (0/1)],
    ![((2172/35) + J*(-944/35)), ((7096/105) + J*(-384/35)), ((346/7) + J*(48/7)), (-288/7), (0/1), (0/1), (0/1)],
    ![((-1856/35) + J*(768/35)), ((-344/35) + J*(-128/5)), ((120/1) + J*(-384/35)), (864/7), (0/1), (0/1), (0/1)],
    ![((-6016/105) + J*(832/35)), ((-6064/35) + J*(1536/35)), ((-2656/7) + J*(96/35)), ((-456/5) + J*(-128/35)), (432/7), (0/1), (0/1)],
    ![((912/7) + J*(-1536/35)), ((6064/21) + J*(-384/35)), ((8448/35) + J*(768/35)), ((-1536/5) + J*(64/35)), (-3456/35), (0/1), (0/1)],
    ![((-4096/105) + J*(384/35)), ((-2336/35) + J*(-1536/35)), ((18544/35) + J*(-384/35)), (10336/21), ((764/35) + J*(16/35)), (-1152/35), (0/1)],
    ![((-512/5) + J*(1024/35)), ((-2624/7) + J*(768/35)), (-27232/35), ((-1504/15) + J*(-128/35)), (1632/7), (576/35), (0/1)],
    ![((704/7) + J*(-512/35)), (2560/7), ((4448/35) + J*(384/35)), (-4288/7), (-11992/105), (16/35), (144/35)],
    ![(2432/105), ((-128/35) + J*(-512/35)), (4992/7), (30272/105), (-144/35), (-1296/35), (0/1)],
    ![((-5056/105) + J*(256/35)), (-2304/7), (-10688/35), (512/35), (4608/35), (0/1), (0/1)],
    ![(1024/35), (10496/105), (-128/5), (-1152/5), (0/1), (0/1), (0/1)],
    ![(1664/105), (768/35), (6912/35), (0/1), (0/1), (0/1), (0/1)],
    ![(-256/35), (-2304/35), (0/1), (0/1), (0/1), (0/1), (0/1)]]) l k

theorem generalMeanPolynomial_identity_0 (J : ℚ) :
    generalMeanJointCleared J 0 = tensorOfFn 6 15 (generalMeanCoefficients0 J) := by
  apply tensor_eq_of_eval
  intro a b
  simp [generalMeanJointCleared, majorantCleared, majorantHQ,
    majorantAQ, majorantBQ, padeDQ, padeNQ, comparisonZQ, tensorOfFn,
    generalMeanCoefficients0, Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_succ, Polynomial.eval₂_monomial,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_monomial]
  ring

def generalMeanCoefficients1 (J : ℚ) : Fin 7 → Fin 16 → ℚ :=
  fun k l => (![![((-23/12) + J*(1/1)), (-2/1), (4/1), (0/1), (0/1), (0/1), (0/1)],
    ![((184/21) + J*(-32/7)), (64/7), (-128/7), (0/1), (0/1), (0/1), (0/1)],
    ![((-1111/84) + J*(48/7)), ((-146/21) + J*(-32/7)), (368/7), (-128/7), (0/1), (0/1), (0/1)],
    ![((-34/5) + J*(192/35)), ((-1824/35) + J*(96/7)), (-2752/35), (384/7), (0/1), (0/1), (0/1)],
    ![((1396/35) + J*(-944/35)), ((17152/105) + J*(-384/35)), ((622/35) + J*(48/7)), (-4576/35), (192/7), (0/1), (0/1)],
    ![((-992/35) + J*(768/35)), ((-5536/35) + J*(-128/5)), ((1656/5) + J*(-384/35)), (4864/35), (-1536/35), (0/1), (0/1)],
    ![((-2956/105) + J*(832/35)), ((-6976/35) + J*(1536/35)), ((-24564/35) + J*(96/35)), ((-40/7) + J*(-128/35)), (128/1), (-512/35), (0/1)],
    ![((1152/35) + J*(-1536/35)), ((65312/105) + J*(-384/35)), ((14576/35) + J*(768/35)), ((-22336/35) + J*(64/35)), (-640/7), (256/35), (0/1)],
    ![((496/21) + J*(384/35)), ((-3168/7) + J*(-1536/35)), ((36024/35) + J*(-384/35)), (80288/105), ((32/35) + J*(16/35)), (-416/7), (64/35)],
    ![((-64/5) + J*(1024/35)), ((-17888/35) + J*(768/35)), (-10368/7), ((-16144/105) + J*(-128/35)), (15136/35), (512/35), (0/1)],
    ![((-1312/35) + J*(-512/35)), (4224/5), ((13344/35) + J*(384/35)), (-40832/35), (-17572/105), (0/1), (256/35)],
    ![(1024/21), ((-1472/5) + J*(-512/35)), (48128/35), (53024/105), (32/35), (-2368/35), (0/1)],
    ![((4736/105) + J*(256/35)), (-4096/7), (-21792/35), (-256/35), (8704/35), (0/1), (0/1)],
    ![(-512/35), (3968/15), (768/35), (-15872/35), (0/1), (0/1), (0/1)],
    ![(1472/105), (-1024/35), (2048/5), (0/1), (0/1), (0/1), (0/1)],
    ![(512/35), (-1024/7), (0/1), (0/1), (0/1), (0/1), (0/1)]]) l k

theorem generalMeanPolynomial_identity_1 (J : ℚ) :
    generalMeanJointCleared J 1 = tensorOfFn 6 15 (generalMeanCoefficients1 J) := by
  apply tensor_eq_of_eval
  intro a b
  simp [generalMeanJointCleared, majorantCleared, majorantHQ,
    majorantAQ, majorantBQ, padeDQ, padeNQ, comparisonZQ, tensorOfFn,
    generalMeanCoefficients1, Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_succ, Polynomial.eval₂_monomial,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_monomial]
  ring

def generalMeanCoefficients2 (J : ℚ) : Fin 7 → Fin 16 → ℚ :=
  fun k l => (![![((-13/5) + J*(1/1)), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![((416/35) + J*(-32/7)), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![((-603/35) + J*(48/7)), ((268/105) + J*(-32/7)), (24/1), (0/1), (0/1), (0/1), (0/1)],
    ![((-4378/525) + J*(192/35)), ((-2204/105) + J*(96/7)), (-768/7), (0/1), (0/1), (0/1), (0/1)],
    ![((20276/525) + J*(-944/35)), ((14312/175) + J*(-384/35)), ((19678/105) + J*(48/7)), (-768/7), (0/1), (0/1), (0/1)],
    ![((-528/175) + J*(768/35)), ((-94216/525) + J*(-128/5)), ((28232/175) + J*(-384/35)), (2304/7), (0/1), (0/1), (0/1)],
    ![((-17624/525) + J*(832/35)), ((896/15) + J*(1536/35)), ((-156888/175) + J*(96/35)), ((-163448/525) + J*(-128/35)), (1152/7), (0/1), (0/1)],
    ![((-34624/525) + J*(-1536/35)), ((72224/175) + J*(-384/35)), ((520432/525) + J*(768/35)), ((-369296/525) + J*(64/35)), (-9216/35), (0/1), (0/1)],
    ![((26144/175) + J*(384/35)), ((-19232/25) + J*(-1536/35)), ((4096/5) + J*(-384/35)), (225856/175), ((48956/525) + J*(16/35)), (-3072/35), (0/1)],
    ![((64/1) + J*(1024/35)), ((-2496/175) + J*(768/35)), (-344896/175), ((-90464/175) + J*(-128/35)), (12640/21), (1536/35), (0/1)],
    ![((-133376/525) + J*(-512/35)), (143872/175), ((174176/175) + J*(384/35)), (-4480/3), (-53552/175), (-352/105), (384/35)],
    ![(22272/175), ((-16000/21) + J*(-512/35)), (1536/1), (136576/175), (1056/35), (-3456/35), (0/1)],
    ![((32576/175) + J*(256/35)), (-9728/21), (-148608/175), (-11264/105), (12288/35), (0/1), (0/1)],
    ![(-9728/105), (54784/175), (2816/15), (-3072/5), (0/1), (0/1), (0/1)],
    ![(3328/175), (-5632/35), (18432/35), (0/1), (0/1), (0/1), (0/1)],
    ![(5632/105), (-6144/35), (0/1), (0/1), (0/1), (0/1), (0/1)]]) l k

theorem generalMeanPolynomial_identity_2 (J : ℚ) :
    generalMeanJointCleared J 2 = tensorOfFn 6 15 (generalMeanCoefficients2 J) := by
  apply tensor_eq_of_eval
  intro a b
  simp [generalMeanJointCleared, majorantCleared, majorantHQ,
    majorantAQ, majorantBQ, padeDQ, padeNQ, comparisonZQ, tensorOfFn,
    generalMeanCoefficients2, Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_succ, Polynomial.eval₂_monomial,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_monomial]
  ring

def generalMeanCoefficients3 (J : ℚ) : Fin 7 → Fin 16 → ℚ :=
  fun k l => (![![((-113/60) + J*(1/1)), (-2/1), (4/1), (0/1), (0/1), (0/1), (0/1)],
    ![((904/105) + J*(-32/7)), (64/7), (-128/7), (0/1), (0/1), (0/1), (0/1)],
    ![((-5473/420) + J*(48/7)), ((-746/105) + J*(-32/7)), (368/7), (-128/7), (0/1), (0/1), (0/1)],
    ![((-3394/525) + J*(192/35)), ((-1808/35) + J*(96/7)), (-2752/35), (384/7), (0/1), (0/1), (0/1)],
    ![((20348/525) + J*(-944/35)), ((85648/525) + J*(-384/35)), ((18/1) + J*(48/7)), (-4576/35), (192/7), (0/1), (0/1)],
    ![((-4864/175) + J*(768/35)), ((-83728/525) + J*(-128/5)), ((57896/175) + J*(-384/35)), (4864/35), (-1536/35), (0/1), (0/1)],
    ![((-13892/525) + J*(832/35)), ((-6912/35) + J*(1536/35)), ((-122844/175) + J*(96/35)), ((-3064/525) + J*(-128/35)), (128/1), (-512/35), (0/1)],
    ![((768/25) + J*(-1536/35)), ((46688/75) + J*(-384/35)), ((73072/175) + J*(768/35)), ((-335008/525) + J*(64/35)), (-640/7), (256/35), (0/1)],
    ![((12176/525) + J*(384/35)), ((-79712/175) + J*(-1536/35)), ((5144/5) + J*(-384/35)), (401504/525), ((488/525) + J*(16/35)), (-416/7), (64/35)],
    ![((-1088/105) + J*(1024/35)), ((-89248/175) + J*(768/35)), (-259328/175), ((-80816/525) + J*(-128/35)), (15136/35), (512/35), (0/1)],
    ![((-20128/525) + J*(-512/35)), (148096/175), ((66848/175) + J*(384/35)), (-40832/35), (-87868/525), (0/1), (256/35)],
    ![(3584/75), ((-6208/21) + J*(-512/35)), (48128/35), (265184/525), (32/35), (-2368/35), (0/1)],
    ![((24064/525) + J*(256/35)), (-4096/7), (-109024/175), (-256/35), (8704/35), (0/1), (0/1)],
    ![(-512/35), (139136/525), (768/35), (-15872/35), (0/1), (0/1), (0/1)],
    ![(7232/525), (-1024/35), (2048/5), (0/1), (0/1), (0/1), (0/1)],
    ![(512/35), (-1024/7), (0/1), (0/1), (0/1), (0/1), (0/1)]]) l k

theorem generalMeanPolynomial_identity_3 (J : ℚ) :
    generalMeanJointCleared J 3 = tensorOfFn 6 15 (generalMeanCoefficients3 J) := by
  apply tensor_eq_of_eval
  intro a b
  simp [generalMeanJointCleared, majorantCleared, majorantHQ,
    majorantAQ, majorantBQ, padeDQ, padeNQ, comparisonZQ, tensorOfFn,
    generalMeanCoefficients3, Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_succ, Polynomial.eval₂_monomial,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_monomial]
  ring

def generalMeanCoefficients4 (J : ℚ) : Fin 7 → Fin 16 → ℚ :=
  fun k l => (![![((-257/120) + J*(1/1)), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![((1028/105) + J*(-32/7)), (0/1), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![((-12217/840) + J*(48/7)), ((923/105) + J*(-32/7)), (9/1), (0/1), (0/1), (0/1), (0/1)],
    ![((-2111/175) + J*(192/35)), ((-189/5) + J*(96/7)), (-288/7), (0/1), (0/1), (0/1), (0/1)],
    ![((10712/175) + J*(-944/35)), ((35396/525) + J*(-384/35)), ((248/5) + J*(48/7)), (-288/7), (0/1), (0/1), (0/1)],
    ![((-9208/175) + J*(768/35)), ((-1892/175) + J*(-128/5)), ((20952/175) + J*(-384/35)), (864/7), (0/1), (0/1), (0/1)],
    ![((-4202/75) + J*(832/35)), ((-6016/35) + J*(1536/35)), ((-66418/175) + J*(96/35)), ((-15976/175) + J*(-128/35)), (432/7), (0/1), (0/1)],
    ![((3216/25) + J*(-1536/35)), ((151792/525) + J*(-384/35)), ((42384/175) + J*(768/35)), ((-53752/175) + J*(64/35)), (-3456/35), (0/1), (0/1)],
    ![((-20648/525) + J*(384/35)), ((-12064/175) + J*(-1536/35)), ((18532/35) + J*(-384/35)), (258448/525), ((546/25) + J*(16/35)), (-1152/35), (0/1)],
    ![((-704/7) + J*(1024/35)), ((-65456/175) + J*(768/35)), (-136256/175), ((-52712/525) + J*(-128/35)), (1632/7), (576/35), (0/1)],
    ![((17488/175) + J*(-512/35)), (64192/175), ((22336/175) + J*(384/35)), (-4288/7), (-59966/525), (16/35), (144/35)],
    ![(11776/525), ((-32/7) + J*(-512/35)), (4992/7), (151408/525), (-144/35), (-1296/35), (0/1)],
    ![((-24992/525) + J*(256/35)), (-2304/7), (-53488/175), (512/35), (4608/35), (0/1), (0/1)],
    ![(1024/35), (52672/525), (-128/5), (-1152/5), (0/1), (0/1), (0/1)],
    ![(8224/525), (768/35), (6912/35), (0/1), (0/1), (0/1), (0/1)],
    ![(-256/35), (-2304/35), (0/1), (0/1), (0/1), (0/1), (0/1)]]) l k

theorem generalMeanPolynomial_identity_4 (J : ℚ) :
    generalMeanJointCleared J 4 = tensorOfFn 6 15 (generalMeanCoefficients4 J) := by
  apply tensor_eq_of_eval
  intro a b
  simp [generalMeanJointCleared, majorantCleared, majorantHQ,
    majorantAQ, majorantBQ, padeDQ, padeNQ, comparisonZQ, tensorOfFn,
    generalMeanCoefficients4, Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_succ, Polynomial.eval₂_monomial,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_monomial]
  ring

def generalMeanCoefficients5 (J : ℚ) : Fin 9 → Fin 16 → ℚ :=
  fun k l => (![![((-19102951/8000000) + J*(1/1)), (1437039/400000), (-328957/20000), (25197/1000), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![((2728993/250000) + J*(-32/7)), (-1437039/87500), (328957/4375), (-100788/875), (0/1), (0/1), (0/1), (0/1), (0/1)],
    ![((-127888713/8000000) + J*(48/7)), ((9148073/280000) + J*(-32/7)), (-1182353/10000), (24309/100), (-13851/350), (0/1), (0/1), (0/1), (0/1)],
    ![((-3412984769/210000000) + J*(192/35)), ((5589023/3500000) + J*(96/7)), (-3900371/35000), (-1230707/8750), (-12/125), (0/1), (0/1), (0/1), (0/1)],
    ![((2031030821/26250000) + J*(-944/35)), ((-133695739/1250000) + J*(-384/35)), ((3175867/5600) + J*(48/7)), (-37183379/175000), (1326121/8750), (-151266/875), (0/1), (0/1), (0/1)],
    ![((-149663687/2187500) + J*(768/35)), ((4580036171/26250000) + J*(-128/5)), ((-1205078297/2187500) + J*(-384/35)), (69197493/109375), (5007924/21875), (3327264/4375), (0/1), (0/1), (0/1)],
    ![((-4090730507/52500000) + J*(832/35)), ((14440053/2187500) + J*(1536/35)), ((-9754398177/17500000) + J*(96/35)), ((-5248322377/6562500) + J*(-128/35)), (-207813729/109375), (-16051172/21875), (1865208/4375), (0/1), (0/1)],
    ![((4776473/25000) + J*(-1536/35)), ((-311692349/1093750) + J*(-384/35)), ((6060868971/4375000) + J*(768/35)), ((2809942859/2625000) + J*(64/35)), (75386959/43750), (-1173622/625), (-137112/175), (0/1), (0/1)],
    ![((-322761951/4375000) + J*(384/35)), ((24132191/78125) + J*(-1536/35)), ((-1117192411/1750000) + J*(-384/35)), (36831841/312500), ((149652255691/52500000) + J*(16/35)), (3342096367/875000), (9525219/43750), (-1159398/4375), (0/1)],
    ![((-74675807/468750) + J*(1024/35)), ((32520501/437500) + J*(768/35)), (-2393155609/2187500), ((-4152366599/1875000) + J*(-128/35)), (-3215044992/546875), (-15461184/15625), (40131776/21875), (604896/4375), (0/1)],
    ![((238121959/1312500) + J*(-512/35)), (-182435052/546875), ((1271158711/1093750) + J*(384/35)), (3056386573/1093750), (19910095911/17500000), (-10248438437/2187500), (-105308137/109375), (-48796/21875), (151224/4375)],
    ![(5925739/546875), ((120389333/656250) + J*(-512/35)), (-88733861/546875), (103720367/312500), (23098666671/4375000), (536175251/218750), (26742/3125), (-1361016/4375), (0/1)],
    ![((-338409167/3281250) + J*(256/35)), (2417496/21875), (-227790621/312500), (-1313624701/546875), (-291469924/109375), (454288/21875), (4839168/4375), (0/1), (0/1)],
    ![(29706884/546875), (-62899671/546875), (153292933/546875), (109991492/109375), (-3314704/21875), (-1209792/625), (0/1), (0/1), (0/1)],
    ![(2728993/156250), (18189936/546875), (2752/15625), (5720832/21875), (7258752/4375), (0/1), (0/1), (0/1), (0/1)],
    ![(-10853442/546875), (4379672/109375), (-3250784/21875), (-2419584/4375), (0/1), (0/1), (0/1), (0/1), (0/1)]]) l k

theorem generalMeanPolynomial_identity_5 (J : ℚ) :
    generalMeanJointCleared J 5 = tensorOfFn 8 15 (generalMeanCoefficients5 J) := by
  apply tensor_eq_of_eval
  intro a b
  simp [generalMeanJointCleared, majorantCleared, majorantHQ,
    majorantAQ, majorantBQ, padeDQ, padeNQ, comparisonZQ, tensorOfFn,
    generalMeanCoefficients5, Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_succ, Polynomial.eval₂_monomial,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_monomial]
  ring

def generalMeanCoefficients6 (J : ℚ) : Fin 5 → Fin 1 → ℚ :=
  fun k l => (![![((-671/100) + J*(1/1)), (2/1), (671/50), (-671/50), (671/100)]]) l k

theorem generalMeanPolynomial_identity_6 (J : ℚ) :
    C (C J-generalMeanNormQ (671/100)) = tensorOfFn 4 0 (generalMeanCoefficients6 J) := by
  apply tensor_eq_of_eval
  intro a b
  simp [generalMeanNormQ, tensorOfFn,
    generalMeanCoefficients6, Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_succ,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_monomial]
  ring

def generalMeanCoefficients7 (J : ℚ) : Fin 5 → Fin 1 → ℚ :=
  fun k l => (![![((-563/100) + J*(1/1)), (2/1), (563/50), (-563/50), (563/100)]]) l k

theorem generalMeanPolynomial_identity_7 (J : ℚ) :
    C (C J-generalMeanNormQ (563/100)) = tensorOfFn 4 0 (generalMeanCoefficients7 J) := by
  apply tensor_eq_of_eval
  intro a b
  simp [generalMeanNormQ, tensorOfFn,
    generalMeanCoefficients7, Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_succ,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_monomial]
  ring

end SingularValueBounds.KL.Certificates
