import SingularValueBounds.KL.Lower.EndpointCertificates
import SingularValueBounds.KL.Lower.EndpointBlocks

/-! # Real interpretation of the endpoint lower-cost certificates
The remaining premises are finite rational polynomial identities and signs.
Every evaluation identity and whole-interval consequence is proved here. -/
open Polynomial Set
open scoped Polynomial BigOperators
namespace SingularValueBounds.KL
open Certificates
noncomputable section
set_option maxHeartbeats 1000000

def endpointTableA (i : Fin 2) (k : ℝ) : ℝ :=
  (endpointTheta i : ℝ)*k+(1-(endpointTheta i : ℝ))*(73/55)

def endpointOScalar (i : Fin 2) (k x : ℝ) : ℝ :=
  endpointTableA i k+1/(2*(endpointXi i : ℝ))+
    k^2*endpointG (endpointTableA i k) (endpointC i) (endpointXi i) k+
    (1-k^2)*endpointG (endpointTableA i k) (endpointC i) (endpointXi i) x

def endpointNScalar (i : Fin 2) (k x : ℝ) : ℝ :=
  endpointTableA i k-(endpointC i : ℝ)*k^3+
    2*k^2*endpointComparisonEigen (endpointTableA i k) (endpointC i) k+
    (1-k^2)/(endpointChi i : ℝ)+
    (1-k^2)*endpointN (endpointTableA i k) (endpointC i) (endpointChi i) x

lemma endpointAPoly_eval (i : Fin 2) (k : ℝ) :
    realEval (endpointAPoly i) k = endpointTableA i k := by
  simp only [realEval, endpointAPoly, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Rat.coe_castHom, endpointTableA]
  push_cast
  rfl

lemma endpointGPoly_eval (i : Fin 2) (k x : ℝ) :
    realEval₂ (endpointGPoly i) k x =
      endpointG (endpointTableA i k) (endpointC i) (endpointXi i) x := by
  simp only [realEval₂, endpointGPoly, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.coe_eval₂RingHom, Rat.coe_castHom]
  rw [show Polynomial.eval₂ (Rat.castHom ℝ) k (endpointAPoly i) =
    endpointTableA i k from endpointAPoly_eval i k]
  push_cast
  dsimp only [endpointG]
  ring

lemma endpointNPoly_eval (i : Fin 2) (k x : ℝ) :
    realEval₂ (endpointNPoly i) k x =
      endpointN (endpointTableA i k) (endpointC i) (endpointChi i) x := by
  simp only [realEval₂, endpointNPoly, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.coe_eval₂RingHom, Rat.coe_castHom]
  rw [show Polynomial.eval₂ (Rat.castHom ℝ) k (endpointAPoly i) =
    endpointTableA i k from endpointAPoly_eval i k]
  push_cast
  dsimp only [endpointN]
  ring

private lemma realEval_diagonal (p : Polynomial (Polynomial ℚ)) (k : ℝ) :
    realEval (p.eval X) k = realEval₂ p k k := by
  let e := Polynomial.eval₂RingHom (Rat.castHom ℝ) k
  simpa only [realEval, realEval₂, e, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using
    (Polynomial.eval₂_hom (p := p) (f := e) X).symm

lemma endpointOPoly_eval (i : Fin 2) (k x : ℝ) :
    realEval₂ (endpointOPoly i) k x = endpointOScalar i k x := by
  simp only [realEval₂, endpointOPoly, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.eval₂_one, Polynomial.coe_eval₂RingHom, Rat.coe_castHom]
  rw [show Polynomial.eval₂ (Rat.castHom ℝ) k (endpointAPoly i) =
      endpointTableA i k from endpointAPoly_eval i k,
    show Polynomial.eval₂ (Rat.castHom ℝ) k ((endpointGPoly i).eval X) =
      endpointG (endpointTableA i k) (endpointC i) (endpointXi i) k from
        (realEval_diagonal _ _).trans (endpointGPoly_eval i k k),
    show Polynomial.eval₂ (Polynomial.eval₂RingHom (Rat.castHom ℝ) k) x (endpointGPoly i) =
      endpointG (endpointTableA i k) (endpointC i) (endpointXi i) x from endpointGPoly_eval i k x]
  push_cast
  dsimp only [endpointOScalar]

lemma endpointNMajorantPoly_eval (i : Fin 2) (k x : ℝ) :
    realEval₂ (endpointNMajorantPoly i) k x = endpointNScalar i k x := by
  simp only [realEval₂, endpointNMajorantPoly, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.eval₂_one, Polynomial.eval₂_ofNat, Polynomial.coe_eval₂RingHom,
    Rat.coe_castHom]
  rw [show Polynomial.eval₂ (Rat.castHom ℝ) k (endpointAPoly i) =
      endpointTableA i k from endpointAPoly_eval i k,
    show Polynomial.eval₂ (Polynomial.eval₂RingHom (Rat.castHom ℝ) k) x (endpointNPoly i) =
      endpointN (endpointTableA i k) (endpointC i) (endpointChi i) x from endpointNPoly_eval i k x]
  push_cast
  dsimp only [endpointNScalar, endpointComparisonEigen]
  ring

lemma endpointMarginPoly_eval (i : Fin 2) (k x : ℝ) :
    realEval₂ (endpointMarginPoly i) k x =
      73/50-(endpointOmega i : ℝ)*endpointOScalar i k x-
        (1-(endpointOmega i : ℝ))*endpointNScalar i k x := by
  simp only [realEval₂, endpointMarginPoly, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  rw [show Polynomial.eval₂ (Polynomial.eval₂RingHom (Rat.castHom ℝ) k) x (endpointOPoly i) =
      endpointOScalar i k x from endpointOPoly_eval i k x,
    show Polynomial.eval₂ (Polynomial.eval₂RingHom (Rat.castHom ℝ) k) x (endpointNMajorantPoly i) =
      endpointNScalar i k x from endpointNMajorantPoly_eval i k x]
  norm_num

theorem endpoint_table_scalar_bound (h : EndpointTableConditions) (i : Fin 2)
    {k x : ℝ} (hk : k ∈ Icc (endpointKLo i : ℝ) (endpointKHi i : ℝ))
    (hx : x ∈ Icc (0 : ℝ) (7/10)) :
    (endpointOmega i : ℝ)*endpointOScalar i k x+
      (1-(endpointOmega i : ℝ))*endpointNScalar i k x ≤ 73/50 := by
  have hh := endpoint_margin_nonneg h i hk hx
  rw [endpointMarginPoly_eval] at hh
  linarith

/-- A common convex combination of two scalar majorants remains valid after
averaging against the nonnegative remaining spectral weights. -/
theorem endpoint_weighted_average {ι : Type*} (s : Finset ι) (p f g : ι → ℝ)
    {M A B ω cap : ℝ} (hM : 0 < M) (hp : ∀ j ∈ s, 0 ≤ p j)
    (hsum : ∑ j ∈ s, p j = M)
    (hpoint : ∀ j ∈ s, ω*(A+M*f j)+(1-ω)*(B+M*g j) ≤ cap) :
    ω*(A+∑ j ∈ s, p j*f j)+(1-ω)*(B+∑ j ∈ s, p j*g j) ≤ cap := by
  have hs := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hpoint j hj) (hp j hj))
  have he : (∑ j ∈ s, p j*(ω*(A+M*f j)+(1-ω)*(B+M*g j))) =
      M*(ω*(A+∑ j ∈ s, p j*f j)+(1-ω)*(B+∑ j ∈ s, p j*g j)) := by
    calc
      _ = (∑ j ∈ s, p j)*(ω*A+(1-ω)*B)+
          M*(ω*(∑ j ∈ s, p j*f j)+(1-ω)*(∑ j ∈ s, p j*g j)) := by
        simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [hsum]; ring
  rw [he, ← Finset.sum_mul, hsum] at hs
  exact (mul_le_mul_iff_right₀ hM).mp hs

def endpointOrdinaryMajorant {ι : Type*} [Fintype ι] (r : ι → ℝ) (A c ξ : ℝ) : ℝ :=
  A+1/(2*ξ)+∑ i, r i^2*endpointG A c ξ (r i)

theorem endpoint_table_spectral_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : EndpointTableConditions) (i : Fin 2) (r : ι → ℝ) (top : ι)
    (h2 : spectralMoment r 2=1)
    (hk : r top ∈ Icc (endpointKLo i : ℝ) (endpointKHi i : ℝ))
    (hrest : ∀ j, j ≠ top → r j ∈ Icc (0 : ℝ) (7/10)) :
    (endpointOmega i : ℝ)*endpointOrdinaryMajorant r (endpointTableA i (r top)) (endpointC i) (endpointXi i)+
      (1-(endpointOmega i : ℝ))*endpointRankOneMajorant r top
        (endpointTableA i (r top)) (endpointC i) (endpointChi i) ≤ 73/50 := by
  have hsplit := endpointRestMoment_split r top 2
  rw [h2] at hsplit
  have hsum : (∑ j ∈ Finset.univ.erase top, r j^2)=1-r top^2 := by
    change endpointRestMoment r top 2=1-r top^2
    linarith
  have hk01 : 0 ≤ r top ∧ r top < 1 := by
    fin_cases i <;> norm_num [endpointKLo,endpointKHi] at hk <;>
      exact ⟨by linarith [hk.1],by linarith [hk.2]⟩
  have hM : 0 < 1-r top^2 := by nlinarith [hk01.1,hk01.2]
  let A := endpointTableA i (r top)
  let c := (endpointC i : ℝ)
  let ξ := (endpointXi i : ℝ)
  let χ := (endpointChi i : ℝ)
  have hh := endpoint_weighted_average (Finset.univ.erase top) (fun j => r j^2)
    (fun j => endpointG A c ξ (r j)) (fun j => endpointN A c χ (r j))
    (A := A+1/(2*ξ)+r top^2*endpointG A c ξ (r top))
    (B := A-c*r top^3+2*r top^2*endpointComparisonEigen A c (r top)+(1-r top^2)/χ)
    hM (fun _ _ => sq_nonneg _) hsum (fun j hj => by
      exact endpoint_table_scalar_bound h i hk (hrest j (Finset.mem_erase.mp hj).1))
  have hg : (∑ j, r j^2*endpointG A c ξ (r j)) =
      r top^2*endpointG A c ξ (r top)+
        ∑ j ∈ Finset.univ.erase top, r j^2*endpointG A c ξ (r j) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ top)).symm
  change (endpointOmega i : ℝ)*endpointOrdinaryMajorant r A c ξ+
    (1-(endpointOmega i : ℝ))*endpointRankOneMajorant r top A c χ ≤ 73/50
  unfold endpointOrdinaryMajorant endpointRankOneMajorant
  rw [hg]
  simpa only [add_assoc] using hh

theorem endpoint_table_min_majorant_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : EndpointTableConditions) (i : Fin 2) (r : ι → ℝ) (top : ι)
    (h2 : spectralMoment r 2=1)
    (hk : r top ∈ Icc (endpointKLo i : ℝ) (endpointKHi i : ℝ))
    (hrest : ∀ j, j ≠ top → r j ∈ Icc (0 : ℝ) (7/10)) :
    min (endpointOrdinaryMajorant r (endpointTableA i (r top)) (endpointC i) (endpointXi i))
      (endpointRankOneMajorant r top (endpointTableA i (r top)) (endpointC i) (endpointChi i)) ≤ 73/50 := by
  have hh := endpoint_table_spectral_bound h i r top h2 hk hrest
  have hω : 0 ≤ (endpointOmega i : ℝ) ∧ (endpointOmega i : ℝ) ≤ 1 := by
    fin_cases i <;> norm_num [endpointOmega]
  let O := endpointOrdinaryMajorant r (endpointTableA i (r top)) (endpointC i) (endpointXi i)
  let N := endpointRankOneMajorant r top (endpointTableA i (r top)) (endpointC i) (endpointChi i)
  have hm : min O N ≤ (endpointOmega i : ℝ)*O+(1-(endpointOmega i : ℝ))*N := by
    calc
      _ = (endpointOmega i : ℝ)*min O N+(1-(endpointOmega i : ℝ))*min O N := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (min_le_left O N) hω.1)
        (mul_le_mul_of_nonneg_left (min_le_right O N) (sub_nonneg.mpr hω.2))
  exact hm.trans hh

/-- The concrete far-spectrum quartic printed in S1.5. -/
def endpointFarScalar (x : ℝ) : ℝ := x/32+1849*x^2/1280-399*x^3/128+245*x^4/256

def endpointFarJ (k : ℝ) : ℝ := k^2*endpointFarScalar k+(1-k^2)*(7/100)

lemma endpointG_far_eq (x : ℝ) : endpointG (5/4) (7/4) (8/5) x = endpointFarScalar x := by
  norm_num [endpointG,endpointFarScalar]
  ring

lemma endpointFarG_eval (x : ℝ) : realEval endpointFarG x = endpointFarScalar x := by
  simp only [realEval, endpointFarG, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Rat.coe_castHom]
  push_cast
  dsimp only [endpointFarScalar]
  ring

lemma endpointFarDerivative_eval (k : ℝ) :
    realEval endpointFarDerivative k = 7/50-3*k/32-1849*k^2/320+1995*k^3/128-735*k^4/128 := by
  simp only [realEval, endpointFarDerivative, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Rat.coe_castHom]
  push_cast
  ring

lemma hasDerivAt_endpointFarJ (k : ℝ) :
    HasDerivAt endpointFarJ (-k*realEval endpointFarDerivative k) k := by
  rw [endpointFarDerivative_eval]
  unfold endpointFarJ endpointFarScalar
  have h1 := (hasDerivAt_id k).div_const (32 : ℝ)
  have h2 := (((hasDerivAt_id k).pow 2).const_mul (1849 : ℝ)).div_const (1280 : ℝ)
  have h3 := (((hasDerivAt_id k).pow 3).const_mul (399 : ℝ)).div_const (128 : ℝ)
  have h4 := (((hasDerivAt_id k).pow 4).const_mul (245 : ℝ)).div_const (256 : ℝ)
  have hg := ((h1.add h2).sub h3).add h4
  have hd := (((hasDerivAt_id k).pow 2).mul hg).add
    (((hasDerivAt_const k (1 : ℝ)).sub ((hasDerivAt_id k).pow 2)).mul_const (7/100))
  convert! hd using 1 <;>
    simp only [Pi.pow_apply, Pi.add_apply, Pi.sub_apply, id_eq] <;> ring

theorem endpoint_far_scalar_le (h : EndpointFarConditions) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : endpointFarScalar x ≤ 7/100 := by
  rw [← endpointFarG_eval]
  exact endpoint_far_g_le h hx

theorem endpoint_far_J_antitone (h : EndpointFarConditions) : AntitoneOn endpointFarJ (Icc (3/4 : ℝ) 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (3/4 : ℝ) 1)
  · intro k _
    exact (hasDerivAt_endpointFarJ k).continuousAt.continuousWithinAt
  · intro k _
    exact (hasDerivAt_endpointFarJ k).hasDerivWithinAt
  · intro k hk
    rw [interior_Icc] at hk
    have hkn : 0 ≤ k := by linarith [hk.1]
    have hn := neg_nonpos.mpr (mul_nonneg hkn
      (endpoint_far_derivative_nonneg h ⟨hk.1.le,hk.2.le⟩))
    simpa only [neg_mul] using hn

theorem endpoint_far_cost_le (h : EndpointFarConditions) {k : ℝ}
    (hk : k ∈ Icc (7/9 : ℝ) 1) : 25/16+endpointFarJ k ≤ 73/50 := by
  have hh := endpoint_far_J_antitone h (show (7/9 : ℝ) ∈ Icc (3/4 : ℝ) 1 by norm_num)
    (show k ∈ Icc (3/4 : ℝ) 1 from ⟨by linarith [hk.1],hk.2⟩) hk.1
  have hbase : 25/16+endpointFarJ (7/9) < (73/50 : ℝ) := by
    norm_num [endpointFarJ,endpointFarScalar]
  linarith

/-- The far-spectrum scalar majorants control the full normalized spectral sum. -/
theorem endpoint_far_spectral_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : EndpointFarConditions) (r : ι → ℝ) (top : ι)
    (h2 : spectralMoment r 2=1) (hk : r top ∈ Icc (7/9 : ℝ) 1)
    (hrest : ∀ j, j ≠ top → r j ∈ Icc (0 : ℝ) 1) :
    endpointOrdinaryMajorant r (5/4) (7/4) (8/5) ≤ 73/50 := by
  have hsum : (∑ j ∈ Finset.univ.erase top, r j^2) = 1-r top^2 := by
    have hs := endpointRestMoment_split r top 2
    rw [h2] at hs
    change endpointRestMoment r top 2 = _
    linarith
  have hterm := Finset.sum_le_sum (s := Finset.univ.erase top) (fun j hj =>
    mul_le_mul_of_nonneg_left (endpoint_far_scalar_le h (hrest j (Finset.mem_erase.mp hj).1))
      (sq_nonneg (r j)))
  rw [← Finset.sum_mul, hsum] at hterm
  have hsplit := (Finset.add_sum_erase Finset.univ
    (fun j => r j^2*endpointFarScalar (r j)) (Finset.mem_univ top)).symm
  have hcost : endpointOrdinaryMajorant r (5/4) (7/4) (8/5) ≤ 25/16+endpointFarJ (r top) := by
    unfold endpointOrdinaryMajorant
    simp_rw [endpointG_far_eq]
    rw [hsplit]
    unfold endpointFarJ
    norm_num
    linarith
  exact hcost.trans (endpoint_far_cost_le h hk)

end
end SingularValueBounds.KL
