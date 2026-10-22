import SingularValueBounds.KL.Upper.GaussianSeries

/-! # Endpoint MGF coefficient arithmetic (supplementary S1.6.4)

All recurrence arguments and these small base cases are proved in Lean.
The three rows are the printed concentrated-spectrum witnesses.
-/
open scoped BigOperators
namespace SingularValueBounds.KL
noncomputable section
set_option maxHeartbeats 1200000

def endpointLowCoefficient (p : ℕ) : ℝ :=
  (16/21 : ℝ)*(13/2 : ℝ)^(p-1)/(p.factorial : ℝ)+
    (5/21 : ℝ)*tailMomentSeries p (13/2) 2

theorem endpointLowCoefficient_second : endpointLowCoefficient 2=9/2 := by
  norm_num [endpointLowCoefficient,tailMomentSeries,Finset.sum_range_succ]

theorem endpointLowCoefficient_higher {p : ℕ} (hp : 3 ≤ p) :
    endpointLowCoefficient p ≤ (4 : ℝ)^(p-1) := by
  have hbase3 : endpointLowCoefficient 3 ≤ (4 : ℝ)^2 := by
    norm_num [endpointLowCoefficient,tailMomentSeries,Finset.sum_range_succ]
  by_cases hp3 : p=3
  · simpa [hp3] using hbase3
  have hp4 : 4 ≤ p := by omega
  have hbase4 : endpointLowCoefficient 4 ≤ (4 : ℝ)^3 := by
    norm_num [endpointLowCoefficient,tailMomentSeries,Finset.sum_range_succ]
  have hstep (n : ℕ) (hn : 4 ≤ n) : endpointLowCoefficient (n+1) ≤ 4*endpointLowCoefficient n := by
    have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hn4 : (4 : ℝ)≤n := by exact_mod_cast hn
    have hratio : (2 : ℝ)+(13/2 : ℝ)/n ≤4 := by
      have hdiv : (13/2 : ℝ)/n ≤2 := (div_le_iff₀ hn0).2 (by linarith)
      linarith
    have hT := tailMomentSeries_succ_le (show 1≤n by omega)
      (A := (13/2 : ℝ)) (s := 2) (by norm_num) (by norm_num)
    have hT0 := tailMomentSeries_nonneg (p := n) (A := (13/2 : ℝ)) (s := 2)
      (by norm_num) (by norm_num)
    have hA : (13/2 : ℝ)^n/((n+1).factorial : ℝ) ≤
        4*((13/2 : ℝ)^(n-1)/(n.factorial : ℝ)) := by
      have he : (13/2 : ℝ)^n/((n+1).factorial : ℝ) =
          ((13/2 : ℝ)/(n+1))*((13/2 : ℝ)^(n-1)/(n.factorial : ℝ)) := by
        rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
        rw [show n=(n-1)+1 by omega,pow_succ]
        field_simp
        <;> ring
      rw [he]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply (div_le_iff₀ (by positivity : (0 : ℝ)<n+1)).2
      linarith
    have hTT := hT.trans (mul_le_mul_of_nonneg_right hratio hT0)
    dsimp [endpointLowCoefficient]
    have h := add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ)≤16/21))
      (mul_le_mul_of_nonneg_left hTT (by norm_num : (0 : ℝ)≤5/21))
    convert h using 1 <;> ring
  clear hp hp3 hbase3
  induction p,hp4 using Nat.le_induction with
  | base => simpa using hbase4
  | succ n hn ih =>
    have hh := (hstep n hn).trans (mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ)≤4))
    have hpw : (4 : ℝ)^n=4*(4 : ℝ)^(n-1) := by
      calc
        _ = (4 : ℝ)^((n-1)+1) := congrArg _ (by omega)
        _ = _ := by rw [pow_succ]; ring
    simpa only [Nat.add_sub_cancel,hpw] using hh

structure EndpointRareRow where
  probability : ℝ
  cutoff : ℝ
  zeta : ℝ

def endpointRareRow (i : Fin 3) : EndpointRareRow :=
  if i=0 then ⟨91/2000,947/100,(47/50 : ℝ)^4+(1-(47/50 : ℝ)^2)^2⟩
  else if i=1 then ⟨7/160,239/25,(19/20 : ℝ)^4+(1-(19/20 : ℝ)^2)^2⟩
  else ⟨19/500,10,1⟩

def endpointRareCoefficient (i : Fin 3) (p : ℕ) : ℝ :=
  (if p=2 then 1/2+(endpointRareRow i).zeta else gaussianSquareCoefficient p)+
    (endpointRareRow i).probability*shiftedExponentialCoefficient p
      (endpointRareRow i).cutoff (50/23)

theorem endpointRareCoefficient_second (i : Fin 3) : endpointRareCoefficient i 2<9/2 := by
  fin_cases i <;> norm_num [endpointRareCoefficient,endpointRareRow,
    shiftedExponentialCoefficient,tailMomentSeries,Finset.sum_range_succ]

theorem endpointRareCoefficient_higher (i : Fin 3) {p : ℕ} (hp : 3≤p) :
    endpointRareCoefficient i p ≤ (4 : ℝ)^(p-1) := by
  have hbase (n : ℕ) (hn : n=3 ∨ n=4 ∨ n=5) :
      endpointRareCoefficient i n ≤ (4 : ℝ)^(n-1) := by
    rcases hn with rfl|rfl|rfl <;> fin_cases i <;>
      norm_num [endpointRareCoefficient,endpointRareRow,gaussianSquareCoefficient,
        shiftedExponentialCoefficient,tailMomentSeries,Finset.sum_range_succ]
  by_cases h5 : p<5
  · exact hbase p (by omega)
  have hp5 : 5≤p := by omega
  have hr0 : 0≤(endpointRareRow i).probability := by fin_cases i <;> norm_num [endpointRareRow]
  have hA0 : 0≤(endpointRareRow i).cutoff := by fin_cases i <;> norm_num [endpointRareRow]
  have hA10 : (endpointRareRow i).cutoff≤10 := by fin_cases i <;> norm_num [endpointRareRow]
  have hstep (n : ℕ) (hn : 5≤n) : endpointRareCoefficient i (n+1) ≤ 4*endpointRareCoefficient i n := by
    have hn5 : (5 : ℝ)≤n := by exact_mod_cast hn
    have hg := gaussianSquareCoefficient_step n
    have hg4 : gaussianSquareCoefficient (n+1) ≤4*gaussianSquareCoefficient n := by
      nlinarith [gaussianSquareCoefficient_nonneg n]
    have hS := shiftedExponentialCoefficient_step n hA0 (by norm_num : (0 : ℝ)≤50/23)
    have hS0 := tailMomentSeries_nonneg (p := n+1) hA0 (by norm_num : (0 : ℝ)≤50/23)
    have hratio : (50/23 : ℝ)+(endpointRareRow i).cutoff/(n+1)≤4 := by
      have hdiv : (endpointRareRow i).cutoff/(n+1)≤4-50/23 :=
        (div_le_iff₀ (by positivity : (0 : ℝ)<n+1)).2 (by nlinarith)
      linarith
    have hSS := hS.trans (mul_le_mul_of_nonneg_right hratio hS0)
    have hh := add_le_add hg4 (mul_le_mul_of_nonneg_left hSS hr0)
    simp only [endpointRareCoefficient,show n≠2 by omega,show n+1≠2 by omega,if_false]
    convert hh using 1 <;> ring
  clear hp h5
  induction p,hp5 using Nat.le_induction with
  | base => exact hbase 5 (Or.inr (Or.inr rfl))
  | succ n hn ih =>
    have hh := (hstep n hn).trans (mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ)≤4))
    have hpw : (4 : ℝ)^n=4*(4 : ℝ)^(n-1) := by
      calc
        _ = (4 : ℝ)^((n-1)+1) := congrArg _ (by omega)
        _ = _ := by rw [pow_succ]; ring
    simpa only [Nat.add_sub_cancel,hpw] using hh

end
end SingularValueBounds.KL
