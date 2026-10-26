import SingularValueBounds.KL.Upper.CertificateData
import SingularValueBounds.KL.Certificates.BernsteinIdentity

/-! Exact upper-rate polynomial leaf certificates.
The explicit rational coefficient vectors are verified by polynomial equality;
all Bernstein coefficient signs are reduced by Lean's kernel. -/
open Polynomial
open scoped BigOperators
namespace SingularValueBounds.KL.Certificates
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem rate_14_leaf_0 :
    IntervalCertificate (ratePolynomial (4/1) (201/5000)) (0/1) (3/8) 27
      (bernsteinCoefficients ((ratePolynomial (4/1) (201/5000)).comp
        (affine (0/1) ((3/8)-(0/1)))) 27) := by
  refine Or.inr ⟨by norm_num, ?_⟩
  let coefficients : Fin 28 → ℚ := ![(984449811456/625),
      (3568630566528/625),
      (200272477968/25),
      (3758555888226/625),
      (2640917927673/1250),
      (-5573372164803/10000),
      (-3965395382631/3200),
      (-3838794827897961/4480000),
      (-25162521551666991/71680000),
      (-39759811127038467/573440000),
      (92426301795838329/4587520000),
      (10668496284277222203/403701760000),
      (11885171319104209083/807403520000),
      (99791590075677982863/16793993216000),
      (259805751517363023387/134351945728000),
      (218498822903269700019/413390602240000),
      (1636502346613557386739/13228499271680000),
      (48156264011279462481/1924145348608000),
      (337986087066694356417/76965813944320000),
      (411096410288708417289/615726511554560000),
      (215589325716935649567/2462906046218240000),
      (27604780375879762893/2814749767106560000),
      (20843436645098754849/22517998136852480000),
      (12971559600106415361/180143985094819840000),
      (12861911416299323769/2882303761517117440000),
      (4799821342117230117/23058430092136939520000),
      (1210642398582364449/184467440737095516160000),
      (157110184983187161/1475739525896764129280000)]
  have hpoly : (ratePolynomial (4/1) (201/5000)).comp
      (affine (0/1) ((3/8)-(0/1))) = Polynomial.ofFn 28 coefficients := by
    rw [Polynomial.ofFn_eq_sum_monomial]
    apply Polynomial.funext
    intro x
    norm_num [coefficients, ratePolynomial, Finset.sum_range_succ, affine, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Fin.sum_univ_succ, Polynomial.eval_finset_sum,
      Polynomial.eval_monomial]
    ring
  rw [hpoly]
  constructor
  · apply polynomial_bernstein_identity
    exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by norm_num) coefficients)
  · simp_rw [bernsteinCoefficients_ofFn]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private theorem rate_14_leaf_1 :
    IntervalCertificate (ratePolynomial (4/1) (201/5000)) (3/8) (3/4) 27
      (bernsteinCoefficients ((ratePolynomial (4/1) (201/5000)).comp
        (affine (3/8) ((3/4)-(3/8)))) 27) := by
  refine Or.inr ⟨by norm_num, ?_⟩
  let coefficients : Fin 28 → ℚ := ![(2742024659999867189872860333844278459/134292296856605535764480000),
      (3942138608434729286392859398609181793/134292296856605535764480000),
      (-266050795146836034637560631294008441/22726388698810167590912000),
      (-605497752186156149253891264455744637/10330176681277348904960000),
      (-284679595865819840644677828557998287/5165088340638674452480000),
      (-658399733441713308092088544669932687/56815971747025418977280000),
      (20073136385617679595182437277698869/737869762948382064640000),
      (201199272224708953174892812764139521/5165088340638674452480000),
      (319108113443162404270673450836710669/10330176681277348904960000),
      (184976602556698034223535623700917783/10330176681277348904960000),
      (17057863343053595514908761618067199/2066035336255469780992000),
      (32552080943133195187256823003684297/10330176681277348904960000),
      (2629640576235942087846603312850299/2582544170319337226240000),
      (104303432958489008848950633864517023/369303816355665223352320000),
      (2277089833389510962795988137875461/33573074214151383941120000),
      (7319913903434137782565129252743/516508834063867445248000),
      (293414911843259601155783431349307/113631943494050837954560000),
      (4237056797665446860329380997251/10330176681277348904960000),
      (585281500886694280609987631919/10330176681277348904960000),
      (69956408014846614879506058213/10330176681277348904960000),
      (3589286814022867152620084937/5165088340638674452480000),
      (8930747286890858683395657/147573952589676412928000),
      (3245798650655366077858749/737869762948382064640000),
      (192202699566588389285967/737869762948382064640000),
      (17872230319922791970253/1475739525896764129280000),
      (614147859729733226391/1475739525896764129280000),
      (13927114183204968939/1475739525896764129280000),
      (157110184983187161/1475739525896764129280000)]
  have hpoly : (ratePolynomial (4/1) (201/5000)).comp
      (affine (3/8) ((3/4)-(3/8))) = Polynomial.ofFn 28 coefficients := by
    rw [Polynomial.ofFn_eq_sum_monomial]
    apply Polynomial.funext
    intro x
    norm_num [coefficients, ratePolynomial, Finset.sum_range_succ, affine, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Fin.sum_univ_succ, Polynomial.eval_finset_sum,
      Polynomial.eval_monomial]
    ring
  rw [hpoly]
  constructor
  · apply polynomial_bernstein_identity
    exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by norm_num) coefficients)
  · simp_rw [bernsteinCoefficients_ofFn]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private theorem rate_14_leaf_2 :
    IntervalCertificate (ratePolynomial (4/1) (201/5000)) (3/4) (3/2) 27
      (bernsteinCoefficients ((ratePolynomial (4/1) (201/5000)).comp
        (affine (3/4) ((3/2)-(3/4)))) 27) := by
  refine Or.inr ⟨by norm_num, ?_⟩
  let coefficients : Fin 28 → ℚ := ![(12734407513187765665361804871/314460325543936000),
      (151571617532431936187265377631/142936511610880000),
      (9291373369493130769177497387231/846623953387520000),
      (6381061711768749887943989788791/120946279055360000),
      (65357682695925630216900543474831/423311976693760000),
      (133493854313462567722593155382969/423311976693760000),
      (18683025144467767988597984229471/38482906972160000),
      (22738272740132059570028032125873/38482906972160000),
      (45164050926112796823720923768073/76965813944320000),
      (37415637683233418190702553329663/76965813944320000),
      (26265361836057016590939415689207/76965813944320000),
      (173811876702554718007210792176867/846623953387520000),
      (410605015533466192549668598851/3848290697216000),
      (132540645488758583925743580940983/2751527848509440000),
      (52154544015625521829912225697043/2751527848509440000),
      (1378109473015320075914238884049/211655988346880000),
      (1652646865114961590779331380351/846623953387520000),
      (7846938151063971741079625007/15393162788864000),
      (8890319877106660744925468187/76965813944320000),
      (248193120354640060861247571/10995116277760000),
      (145118595240660603453107589/38482906972160000),
      (584815899731830268106897/1099511627776000),
      (342173296708179407070417/5497558138880000),
      (32392220792282237740383/5497558138880000),
      (4776473276722944997641/10995116277760000),
      (257849625855540278079/10995116277760000),
      (9084544588875511143/10995116277760000),
      (157110184983187161/10995116277760000)]
  have hpoly : (ratePolynomial (4/1) (201/5000)).comp
      (affine (3/4) ((3/2)-(3/4))) = Polynomial.ofFn 28 coefficients := by
    rw [Polynomial.ofFn_eq_sum_monomial]
    apply Polynomial.funext
    intro x
    norm_num [coefficients, ratePolynomial, Finset.sum_range_succ, affine, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Fin.sum_univ_succ, Polynomial.eval_finset_sum,
      Polynomial.eval_monomial]
    ring
  rw [hpoly]
  constructor
  · apply polynomial_bernstein_identity
    exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by norm_num) coefficients)
  · simp_rw [bernsteinCoefficients_ofFn]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

private theorem rate_14_leaf_3 :
    IntervalCertificate (ratePolynomial (4/1) (201/5000)) (3/2) (3/1) 27
      (bernsteinCoefficients ((ratePolynomial (4/1) (201/5000)).comp
        (affine (3/2) ((3/1)-(3/2)))) 27) := by
  refine Or.inr ⟨by norm_num, ?_⟩
  let coefficients : Fin 28 → ℚ := ![(1599449966270049351464577/468582400),
      (868476322156430910589415559/16400384000),
      (2474013629742627626449643277/6307840000),
      (2335508842282517972792217933/1261568000),
      (19770480774545356581625916253/3153920000),
      (51229802392962865635702893193/3153920000),
      (384644112599067685292934549/11468800),
      (2322738829659775251081573927/40960000),
      (9181073986684580593155955887/114688000),
      (10974340645420157684807318019/114688000),
      (11222920657636231472100438417/114688000),
      (108829334261931818976021334599/1261568000),
      (103929749711151628719213717183/1576960000),
      (25647832292095738094992988589/585728000),
      (74236261838234406864889017231/2928640000),
      (20168512729388819508095021169/1576960000),
      (1012436840639196092942754543/180224000),
      (1228406772218506196745314043/573440000),
      (80963015742498473696107341/114688000),
      (22903806451434176734136577/114688000),
      (2755027804214235770339283/57344000),
      (635846437268074230453/65536),
      (66160108758468731253507/40960000),
      (353939734575135628119/1638400),
      (1829342275696476939627/81920000),
      (137298365023850565327/81920000),
      (1332651958342156449/16384000),
      (157110184983187161/81920000)]
  have hpoly : (ratePolynomial (4/1) (201/5000)).comp
      (affine (3/2) ((3/1)-(3/2))) = Polynomial.ofFn 28 coefficients := by
    rw [Polynomial.ofFn_eq_sum_monomial]
    apply Polynomial.funext
    intro x
    norm_num [coefficients, ratePolynomial, Finset.sum_range_succ, affine, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Fin.sum_univ_succ, Polynomial.eval_finset_sum,
      Polynomial.eval_monomial]
    ring
  rw [hpoly]
  constructor
  · apply polynomial_bernstein_identity
    exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by norm_num) coefficients)
  · simp_rw [bernsteinCoefficients_ofFn]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Nat.choose_eq_fast_choose]
    decide +kernel

theorem concrete_rate_row_14 :
    ∀ cell ∈ (rateTrees 14).leaves 0 ((rateRows 14).1-1),
      IntervalCertificate (ratePolynomial (rateRows 14).1 (rateRows 14).2)
        cell.1 cell.2 27
        (bernsteinCoefficients ((ratePolynomial (rateRows 14).1 (rateRows 14).2).comp
          (affine cell.1 (cell.2-cell.1))) 27) := by
  intro cell hc
  have hrow : rateRows 14 = ((4/1), (201/5000)) := by rfl
  rw [hrow] at hc ⊢
  have hleaves : (rateTrees 14).leaves 0 ((4/1)-1) =
      [((0/1), (3/8)), ((3/8), (3/4)), ((3/4), (3/2)), ((3/2), (3/1))] := by decide +kernel
  rw [hleaves] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact rate_14_leaf_0
  · exact rate_14_leaf_1
  · exact rate_14_leaf_2
  · exact rate_14_leaf_3

end SingularValueBounds.KL.Certificates
