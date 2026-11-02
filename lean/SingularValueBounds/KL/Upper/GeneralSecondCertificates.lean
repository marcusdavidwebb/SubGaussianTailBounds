import SingularValueBounds.KL.Upper.GeneralFourth
import SingularValueBounds.KL.Upper.EndpointCoefficients
import SingularValueBounds.KL.Upper.GeneralSecondData

/-! # Continuous consequences of the general upper second-moment certificates
The remaining assumptions are finite rational comparisons in GeneralSecondData.
No real-variable or probabilistic assertion is accepted from Python. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SingularValueBounds.KL
open Certificates Certificates.NumericalCertificateConditions UpperSecond
noncomputable section
set_option maxHeartbeats 1200000

lemma second_le_up (x : ℚ) : x ≤ secondUpQ x := by
  unfold secondUpQ
  apply (le_div_iff₀ (by norm_num : (0:ℚ)<10^12)).mpr
  exact Int.le_ceil _
lemma second_down_le (x : ℚ) : secondDownQ x ≤ x := by
  unfold secondDownQ
  apply (div_le_iff₀ (by norm_num : (0:ℚ)<10^12)).mpr
  exact Int.floor_le _

lemma one_le_expTaylor (N : ℕ) {x : ℝ} (hx : 0 ≤ x) : 1 ≤ expTaylor N x := by
  have h := Finset.single_le_sum (s := Finset.range (N+1))
    (f := fun j => x^j/(j.factorial:ℝ)) (fun j _ => by positivity)
    (show 0 ∈ Finset.range (N+1) by simp)
  simpa only [expTaylor, pow_zero,Nat.factorial_zero,Nat.cast_one,div_one] using h

lemma second_exp_enclosure {x : ℚ} (hx : -50 < x ∧ x < 50) :
    (secondExpLowerQ x : ℝ) ≤ Real.exp (x:ℝ) ∧ Real.exp (x:ℝ) ≤ (secondExpUpperQ x:ℝ) := by
  have hdown (q : ℚ) : (secondDownQ q : ℝ) ≤ (q:ℝ) := by exact_mod_cast second_down_le q
  have hup (q : ℚ) : (q:ℝ) ≤ (secondUpQ q : ℝ) := by exact_mod_cast second_le_up q
  by_cases hxp : 0 ≤ x
  · have hx0 : (0:ℝ) ≤ x := by exact_mod_cast hxp
    have hx50 : (x:ℝ) < 48+2 := by exact_mod_cast hx.2
    have hl := expTaylor_le_exp 48 hx0
    have hu := exp_le_expTaylorUpper 48 hx0 hx50
    constructor
    · have hq : (secondExpLowerQ x:ℝ) ≤ expTaylor 48 (x:ℝ) := by
        simpa only [secondExpLowerQ,if_pos hxp,cast_expTaylorQ] using hdown (expTaylorQ 48 x)
      exact hq.trans hl
    · exact hu.trans (by simpa only [secondExpUpperQ,if_pos hxp,cast_expTaylorUpperQ] using hup (expTaylorUpperQ 48 x))
  · have hx0 : (0:ℝ) ≤ -(x:ℝ) := by
      have hc : (x:ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hxp)
      linarith
    have hx50 : -(x:ℝ) < 48+2 := by
      have hc : (-50:ℝ) < x := by exact_mod_cast hx.1
      linarith
    have hl := expTaylor_le_exp 48 hx0
    have hu := exp_le_expTaylorUpper 48 hx0 hx50
    have ht : 0 < expTaylor 48 (-(x:ℝ)) := zero_lt_one.trans_le (one_le_expTaylor 48 hx0)
    have htU : 0 < expTaylorUpper 48 (-(x:ℝ)) := (Real.exp_pos _).trans_le hu
    have he : Real.exp (x:ℝ) = 1/Real.exp (-(x:ℝ)) := by rw [Real.exp_neg]; field_simp
    constructor
    · have hq : (secondExpLowerQ x:ℝ) ≤ 1/expTaylorUpper 48 (-(x:ℝ)) := by
        simpa only [secondExpLowerQ,if_neg hxp,Rat.cast_one,Rat.cast_div,cast_expTaylorUpperQ,Rat.cast_neg] using
          hdown (1/expTaylorUpperQ 48 (-x))
      rw [he]
      exact hq.trans (one_div_le_one_div_of_le (Real.exp_pos _) hu)
    · have hq : 1/expTaylor 48 (-(x:ℝ)) ≤ (secondExpUpperQ x:ℝ) := by
        simpa only [secondExpUpperQ,if_neg hxp,Rat.cast_one,Rat.cast_div,cast_expTaylorQ,Rat.cast_neg] using
          hup (1/expTaylorQ 48 (-x))
      rw [he]
      exact (one_div_le_one_div_of_le ht hl).trans hq

lemma second_log_lower {x : ℚ} (hx : 1 ≤ x) : (secondLogLowerQ x:ℝ) ≤ Real.log (x:ℝ) := by
  let k := secondLogCount x
  let r := secondLogReduced x
  have hr : 1 ≤ r := by
    dsimp [r,secondLogReduced,secondLogCount]
    split_ifs with h8 h4 h2 <;> norm_num at * <;> linarith
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have ht := log_argument_transform hr'
  have hcore := logTaylor_le_log_ratio 24 ht.1 ht.2.1
  rw [ht.2.2] at hcore
  have htwo : logTaylor 24 (1/3:ℝ) ≤ Real.log 2 := by
    have h := logTaylor_le_log_ratio 24 (by norm_num : (0:ℝ)≤1/3) (by norm_num : (1/3:ℝ)<1)
    norm_num at h
    exact h
  have hsum := add_le_add hcore (mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg k))
  have heq : (2:ℝ)^k*(r:ℝ)=(x:ℝ) := by
    dsimp [r,secondLogReduced,k]
    push_cast
    field_simp
  rw [← log_pow_two_mul k (by linarith : (0:ℝ)<r),heq] at hsum
  have hround : (secondLogLowerQ x:ℝ) ≤
      logTaylor 24 (((r:ℝ)-1)/((r:ℝ)+1))+(k:ℝ)*logTaylor 24 (1/3) := by
    have h := (Rat.cast_le (K := ℝ)).mpr (second_down_le
      (logTaylorQ 24 ((r-1)/(r+1))+(k:ℚ)*logTaylorQ 24 (1/3)))
    simpa [secondLogLowerQ,r,k] using h
  exact hround.trans hsum

lemma fourth_exclusion_of_certificate {m E x : ℚ} (h : FourthExclusionCertificate m E x) :
    (E:ℝ)*(x:ℝ)^2/2 < (m:ℝ)*Real.log (1+(Real.cosh (x:ℝ)-1)/(m:ℝ)) := by
  have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast h.m_pos
  have hx : -50 < x ∧ x < 50 := ⟨by linarith [h.x_pos],h.x_domain⟩
  have hn : -50 < -x ∧ -x < 50 := by constructor <;> linarith [hx.1,hx.2]
  have hc : (secondCoshLowerQ x:ℝ) ≤ Real.cosh (x:ℝ)-1 := by
    have hl := (second_exp_enclosure hx).1
    have hr := (second_exp_enclosure hn).1
    simp only [secondCoshLowerQ,Rat.cast_sub,Rat.cast_add,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] at *
    rw [Real.cosh_eq]
    push_cast at hr
    linarith
  have ha : 1 ≤ (1+secondCoshLowerQ x/m:ℚ) := by
    have hh := div_nonneg h.cosh_nonneg h.m_pos.le
    linarith
  have hl := second_log_lower ha
  have harg : (0:ℝ) < 1+(secondCoshLowerQ x:ℝ)/(m:ℝ) := by
    have hh : (0:ℝ) ≤ secondCoshLowerQ x := by exact_mod_cast h.cosh_nonneg
    positivity
  have hargle : 1+(secondCoshLowerQ x:ℝ)/(m:ℝ) ≤ 1+(Real.cosh (x:ℝ)-1)/(m:ℝ) :=
    add_le_add_right (div_le_div_of_nonneg_right hc hm.le) 1
  push_cast at hl
  have hlog := hl.trans (Real.log_le_log harg hargle)
  have hmul := mul_le_mul_of_nonneg_left hlog hm.le
  have hfinite : 0 < (secondExclusionQ m E x:ℝ) := by exact_mod_cast h.exclusion
  simp only [secondExclusionQ,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] at hfinite
  linarith

/-- The scalar rare-event remainder from supplementary S1.6.4. -/
def generalRareR (i : Fin 3) (d : ℝ) : ℝ :=
  (endpointRareRow i).probability*Real.exp (-(19/25)*d)/(1+d)*
    (( (endpointRareRow i).cutoff+6*d)^2/2+(50/23)*((endpointRareRow i).cutoff+6*d)+(50/23)^2)

lemma second_row_cast (i : Fin 3) :
    (secondRarePQ i:ℝ)=(endpointRareRow i).probability ∧
    (secondRareAQ i:ℝ)=(endpointRareRow i).cutoff ∧
    (secondRareZQ i:ℝ)=(endpointRareRow i).zeta := by
  fin_cases i <;> norm_num [secondRarePQ,secondRareAQ,secondRareZQ,endpointRareRow]

lemma secondRarePoly_cast (i : Fin 3) (d : ℚ) :
    (secondRarePolyQ i d:ℝ)=((endpointRareRow i).cutoff+6*(d:ℝ))^2/2+
      (50/23)*((endpointRareRow i).cutoff+6*(d:ℝ))+(50/23)^2 := by
  simp only [secondRarePolyQ,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
  rw [(second_row_cast i).2.1]

def generalRareP0 (i : Fin 3) : ℝ :=
  (endpointRareRow i).cutoff^2/2+(50/23)*(endpointRareRow i).cutoff+(50/23)^2
def generalRareP1 (i : Fin 3) : ℝ := 6*((endpointRareRow i).cutoff+50/23)
def generalRareNumerator (i : Fin 3) (d : ℝ) : ℝ :=
  (generalRareP1 i-(1+19/25)*generalRareP0 i)+
    (36-(19/25)*(generalRareP0 i+generalRareP1 i))*d+
    (18-(19/25)*(generalRareP1 i+18))*d^2-(19/25)*18*d^3

lemma generalRareNumerator_nonpos (i : Fin 3) {d : ℝ} (hd : 0 ≤ d) :
    generalRareNumerator i d ≤ 0 := by
  have hc : generalRareP1 i-(1+19/25)*generalRareP0 i ≤ 0 ∧
      36-(19/25)*(generalRareP0 i+generalRareP1 i) ≤ 0 ∧
      18-(19/25)*(generalRareP1 i+18) ≤ 0 := by
    fin_cases i <;> norm_num [generalRareP0,generalRareP1,endpointRareRow]
  have h1 := mul_nonpos_of_nonpos_of_nonneg hc.2.1 hd
  have h2 := mul_nonpos_of_nonpos_of_nonneg hc.2.2 (sq_nonneg d)
  have h3 := pow_nonneg hd 3
  dsimp [generalRareNumerator]
  exact sub_nonpos.mpr ((add_nonpos (add_nonpos hc.1 h1) h2).trans
    (mul_nonneg (by norm_num) h3))

lemma hasDerivAt_generalRareR (i : Fin 3) {d : ℝ} (hd : 0 ≤ d) :
    HasDerivAt (generalRareR i)
      ((endpointRareRow i).probability*Real.exp (-(19/25)*d)/(1+d)^2*generalRareNumerator i d) d := by
  let p := (endpointRareRow i).probability
  let A := (endpointRareRow i).cutoff
  have hP : HasDerivAt (fun x : ℝ => generalRareP0 i+generalRareP1 i*x+18*x^2)
      (generalRareP1 i+36*d) d := by
    convert! ((hasDerivAt_const d (generalRareP0 i)).add
      ((hasDerivAt_id d).const_mul (generalRareP1 i))).add
        (((hasDerivAt_id d).pow 2).const_mul 18) using 1 <;> simp <;> ring
  have hExp := ((hasDerivAt_id d).const_mul (-(19/25 : ℝ))).exp
  have hden : 1+d ≠ 0 := by positivity
  have h := (((hExp.const_mul p).mul hP).div ((hasDerivAt_id d).const_add 1) hden)
  convert! h using 1
  · funext x
    dsimp [generalRareR,generalRareP0,generalRareP1,p]
    ring
  · simp only [id_eq, Pi.mul_apply]
    dsimp [generalRareNumerator,p]
    field_simp
    ring

theorem generalRareR_antitone (i : Fin 3) : AntitoneOn (generalRareR i) (Ici (0 : ℝ)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ))
  · intro d hd
    exact (hasDerivAt_generalRareR i hd).continuousAt.continuousWithinAt
  · intro d hd
    rw [interior_Ici] at hd
    exact (hasDerivAt_generalRareR i hd.le).hasDerivWithinAt
  · intro d hd
    rw [interior_Ici] at hd
    have hp : 0 ≤ (endpointRareRow i).probability := (endpointRareRow_bounds i).1.le
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (generalRareNumerator_nonpos i hd.le)

lemma generalRareR_upper_at_rational (i : Fin 3) {d : ℚ} (hd : 0 ≤ d) (hd50 : -(19/25)*d > -50) :
    generalRareR i (d:ℝ) ≤
      ((secondRarePQ i*secondExpUpperQ (-(19/25)*d)*secondRarePolyQ i d/(1+d):ℚ):ℝ) := by
  have hp : 0 ≤ (endpointRareRow i).probability := (endpointRareRow_bounds i).1.le
  have hA : 0 ≤ (endpointRareRow i).cutoff := (endpointRareRow_bounds i).2.1
  have hdR : (0:ℝ) ≤ d := by exact_mod_cast hd
  have hdomain : -50 < -(19/25)*d ∧ -(19/25)*d < 50 := ⟨hd50,by linarith⟩
  have he := (second_exp_enclosure hdomain).2
  push_cast at he
  have hpoly : 0 ≤ ((endpointRareRow i).cutoff+6*(d:ℝ))^2/2+
      (50/23)*((endpointRareRow i).cutoff+6*(d:ℝ))+(50/23)^2 := by positivity
  have ht := mul_le_mul_of_nonneg_left he hp
  have ht' := mul_le_mul_of_nonneg_right ht hpoly
  have hden : 0 ≤ 1+(d:ℝ) := by positivity
  have h := div_le_div_of_nonneg_right ht' hden
  simp only [generalRareR,div_mul_eq_mul_div]
  convert! h using 1
  all_goals push_cast
  all_goals try simp only [(second_row_cast i).1,secondRarePoly_cast]
  all_goals ring


lemma exp_decay_ratio_antitone {a : ℝ} (ha : 0 ≤ a) :
    AntitoneOn (fun d : ℝ => Real.exp (-a*d)/(1+d)) (Ici (0:ℝ)) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have he : Real.exp (-a*y) ≤ Real.exp (-a*x) := Real.exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ Real.exp (-a*x)/(1+y) := div_le_div_of_nonneg_right he (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_nonneg _) (by positivity) (by linarith)

def generalSecondScalar (i : Fin 3) (m d : ℝ) : ℝ :=
  m*Real.exp (-2*d)*(1+2*(endpointRareRow i).zeta)/(6*(1+d))+generalRareR i d-
    Real.exp (-2*d)/(2*(1+d))

lemma second_zeta_nonneg (i : Fin 3) : 0 ≤ (endpointRareRow i).zeta :=
  (endpointRareRow_bounds i).2.2.2

lemma generalSecondScalar_eq (i : Fin 3) (m d : ℝ) :
    generalSecondScalar i m d =
      m*((1+2*(endpointRareRow i).zeta)/6)*(Real.exp (-2*d)/(1+d))+generalRareR i d-
        (Real.exp (-2*d)/(1+d))/2 := by unfold generalSecondScalar; simp only [div_mul_eq_div_div]; ring

/-- Every point of each closed cell satisfies the scalar second-moment bound. -/
theorem general_second_cell_bound (h : GeneralSecondCertificateConditions) (j : Fin 334)
    (i : Fin 3) {m d : ℝ} (hm : m ≤ (secondCellM j:ℝ))
    (hd : d ∈ Icc (secondCellDLo j:ℝ) (secondCellDHi j:ℝ)) :
    generalSecondScalar i m d ≤ 9/2 := by
  have hc := h.2.2.2.1 j
  let a := secondCellDLo j
  let b := secondCellDHi j
  have ha : (0:ℝ) ≤ a := by exact_mod_cast hc.1
  have hb : (b:ℝ) < 1 := by exact_mod_cast hc.2.2.1
  have hab : (a:ℝ) ≤ b := by exact_mod_cast hc.2.1
  have hd0 : 0 ≤ d := ha.trans hd.1
  have hM : (0:ℝ) < secondCellM j := by exact_mod_cast hc.2.2.2.2.2.2.m_pos
  have hq : 0 ≤ (1+2*(endpointRareRow i).zeta)/6 := by have hz := second_zeta_nonneg i; positivity
  have hExpA : Real.exp (-2*(a:ℝ)) ≤ (secondExpUpperQ (-2*a):ℝ) := by
    have he := (second_exp_enclosure (x := -2*a) ⟨by dsimp [a]; linarith [hc.1,hc.2.1,hc.2.2.1],by linarith [hc.1]⟩).2
    simpa using he
  have hExpB : (secondExpLowerQ (-2*b):ℝ) ≤ Real.exp (-2*(b:ℝ)) := by
    have he := (second_exp_enclosure (x := -2*b) ⟨by dsimp [b]; linarith [hc.2.2.2.1],by linarith [hc.1,hc.2.1]⟩).1
    simpa using he
  have hfU : Real.exp (-2*d)/(1+d) ≤ (secondExpUpperQ (-2*a):ℝ)/(1+(a:ℝ)) :=
    ((exp_decay_ratio_antitone (by norm_num : (0:ℝ)≤2)) ha hd0 hd.1).trans
      (div_le_div_of_nonneg_right hExpA (by positivity))
  have hfL : (secondExpLowerQ (-2*b):ℝ)/(1+(b:ℝ)) ≤ Real.exp (-2*d)/(1+d) :=
    (div_le_div_of_nonneg_right hExpB (by linarith)).trans
      ((exp_decay_ratio_antitone (by norm_num : (0:ℝ)≤2)) hd0 (ha.trans hab) hd.2)
  have hfirst := (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hm hq) (show 0 ≤ Real.exp (-2*d)/(1+d) by exact div_nonneg (Real.exp_nonneg _) (by linarith))).trans
      (mul_le_mul_of_nonneg_left hfU (mul_nonneg hM.le hq))
  have hRare : generalRareR i d ≤
      ((secondRarePQ i*secondExpUpperQ (-(19/25)*a)*secondRarePolyQ i a/(1+a):ℚ):ℝ) :=
    ((generalRareR_antitone i) ha hd0 hd.1).trans (generalRareR_upper_at_rational i hc.1
      (by dsimp [a]; linarith [hc.1,hc.2.1,hc.2.2.1]))
  have hfinite : (secondCellUpperQ j i:ℝ) < 9/2 := by
    have hh := (Rat.cast_lt (K:=ℝ)).2 (h.2.2.2.2 j i)
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
    exact hh
  have heq : (secondCellUpperQ j i:ℝ) =
      (secondCellM j:ℝ)*((1+2*(endpointRareRow i).zeta)/6)*
        ((secondExpUpperQ (-2*a):ℝ)/(1+(a:ℝ)))+
      ((secondRarePQ i*secondExpUpperQ (-(19/25)*a)*secondRarePolyQ i a/(1+a):ℚ):ℝ)-
        ((secondExpLowerQ (-2*b):ℝ)/(1+(b:ℝ)))/2 := by
    dsimp [secondCellUpperQ,a,b]
    push_cast
    rw [(second_row_cast i).2.2]
    simp only [div_mul_eq_div_div]
    ring
  rw [generalSecondScalar_eq]
  rw [heq] at hfinite
  linarith only [hfirst,hRare,hfL,hfinite]

/-- The entire endpoint neighbourhood L≤51/50 uses the single fourth-moment cap4. -/
theorem general_second_small_bound (h : GeneralSecondCertificateConditions) (i : Fin 3)
    {m d : ℝ} (hm : m ≤ 4) (hd : d ∈ Icc (0:ℝ) (1/50)) :
    generalSecondScalar i m d ≤ 9/2 := by
  have hq : 0 ≤ (1+2*(endpointRareRow i).zeta)/6 := by have hz := second_zeta_nonneg i; positivity
  have hfU : Real.exp (-2*d)/(1+d) ≤ 1 := by
    have hh := (exp_decay_ratio_antitone (by norm_num : (0:ℝ)≤2)) (show (0:ℝ)∈Ici 0 by simp) hd.1 hd.1
    simpa using hh
  have he := (second_exp_enclosure (x := -1/25) (by norm_num)).1
  norm_num only [Rat.cast_neg,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at he
  have hfL : (secondExpLowerQ (-1/25):ℝ)/(51/50) ≤ Real.exp (-2*d)/(1+d) := by
    have hh := div_le_div_of_nonneg_right he (by norm_num : (0:ℝ)≤51/50)
    have hh' := (exp_decay_ratio_antitone (by norm_num : (0:ℝ)≤2)) hd.1
      (show (0:ℝ)≤1/50 by norm_num) hd.2
    norm_num at hh'
    convert! hh.trans hh' using 1 <;> norm_num
  have hd0 : 0 ≤ d := hd.1
  have hfirst := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm hq)
      (show 0 ≤ Real.exp (-2*d)/(1+d) by exact div_nonneg (Real.exp_nonneg _) (by linarith))).trans
    (mul_le_mul_of_nonneg_left hfU (mul_nonneg (by norm_num : (0:ℝ)≤4) hq))
  have hRare := (generalRareR_antitone i) (show (0:ℝ)∈Ici 0 by simp) hd.1 hd.1
  have hRare0 : generalRareR i 0=((secondRarePQ i*secondRarePolyQ i 0:ℚ):ℝ) := by
    simp [generalRareR,secondRarePolyQ,(second_row_cast i).1,(second_row_cast i).2.1]
  rw [hRare0] at hRare
  have hfinite : (secondSmallUpperQ i:ℝ) < 9/2 := by
    have hh := (Rat.cast_lt (K:=ℝ)).2 (h.2.2.1 i)
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
    exact hh
  have heq : (secondSmallUpperQ i:ℝ) =
      4*((1+2*(endpointRareRow i).zeta)/6)+((secondRarePQ i*secondRarePolyQ i 0:ℚ):ℝ)-
        ((secondExpLowerQ (-1/25):ℝ)/(51/50))/2 := by
    dsimp [secondSmallUpperQ]
    push_cast
    rw [(second_row_cast i).2.2]
    simp only [div_mul_eq_div_div]
    ring
  rw [generalSecondScalar_eq]
  rw [heq] at hfinite
  linarith only [hfirst,hRare,hfL,hfinite]


end
end SingularValueBounds.KL
