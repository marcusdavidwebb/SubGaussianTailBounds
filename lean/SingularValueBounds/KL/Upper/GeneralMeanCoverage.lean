import SingularValueBounds.KL.Upper.GeneralMeanCells
import SingularValueBounds.KL.Upper.LogdetCertificates

/-! Complete closed spectral coverage, including the clipping boundary aliases. -/
open Set
open scoped BigOperators Matrix
namespace SingularValueBounds.KL
open Certificates
noncomputable section
set_option maxHeartbeats 1600000

lemma general_mean_k_cells_cover {k : ℝ} (hk0 : (2/5:ℝ) ≤ k) (hk1 : k ≤ 1) :
    ∃ i : Fin 48,k∈Icc (((i.val+32:ℚ)/80):ℝ) (((i.val+33:ℚ)/80):ℝ) := by
  let j:=min 79 ⌊80*k⌋₊
  have hk : 0 ≤ 80*k := by linarith
  have hjlo : 32 ≤ j := le_min (by norm_num) ((Nat.le_floor_iff hk).2 (by norm_num;linarith))
  have hjhi : j ≤ 79 := min_le_left _ _
  let i : Fin 48:=⟨j-32,by omega⟩
  have hi : i.val+32=j := by dsimp [i];omega
  have hi' : i.val+33=j+1 := by omega
  have hlo : (j:ℝ) ≤ 80*k := (Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.floor_le hk)
  have hhi : 80*k ≤ (j:ℝ)+1 := by
    by_cases hj : ⌊80*k⌋₊ ≤ 79
    · rw [show j=⌊80*k⌋₊ from min_eq_right hj]
      exact (Nat.lt_floor_add_one (80*k)).le
    · rw [show j=79 from min_eq_left (by omega)]
      norm_num
      linarith
  refine ⟨i,?_⟩
  have hiR : (i.val:ℝ)+32=(j:ℝ) := by exact_mod_cast hi
  have hiR' : (i.val:ℝ)+33=(j:ℝ)+1 := by exact_mod_cast hi'
  push_cast
  constructor <;> linarith

theorem general_mean_cells_cover (h : GeneralMeanCellConditions) {a k : ℝ}
    (hk : k∈Icc (2/5:ℝ) 1) (ha : k^3 ≤ a ∧ a ≤ k) :
    ∃ i : Fin 1330,(generalMeanRows i).box.contains a k := by
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have ha0 : 0 ≤ a := (pow_nonneg hk0 3).trans ha.1
  obtain ⟨ki,hki⟩ := general_mean_k_cells_cover hk.1 hk.2
  obtain ⟨ai,hai⟩ := generalMeanAPartition.covers generalMeanAIntervals 0 1 h.1 (x:=a)
    (by norm_num only [Rat.cast_zero,Rat.cast_one];exact ⟨ha0,ha.2.trans hk.2⟩)
  exact (generalMeanClippedTrees ki ai).covers _ (generalMeanSeed ki ai) (h.2.1 ki ai)
    (by dsimp [generalMeanSeed];positivity) (by dsimp [generalMeanSeed];positivity)
    (by refine ⟨hai,?_⟩;simpa [generalMeanSeed] using hki) ha

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma upperComparisonShapeMean_ratio_bounds {R : Matrix ι ι ℝ} (hR : R.PosDef) :
    (spectralRatio R hR)^3 ≤ upperComparisonShapeMean R hR ∧
      upperComparisonShapeMean R hR ≤ spectralRatio R hR := by
  let x:=upperNormalizedSpectrum R hR
  obtain ⟨hx,h2⟩ := upperNormalizedSpectrum_properties hR
  obtain ⟨top,_,htop⟩ := Finset.exists_mem_eq_sup' (s:=Finset.univ)
    Finset.univ_nonempty hR.isHermitian.eigenvalues
  have ht : x top=spectralRatio R hR := by
    dsimp [x,upperNormalizedSpectrum,spectralRatio,spectralMaximum]
    rw [←htop]
  constructor
  · have hs := Finset.single_le_sum (s:=Finset.univ) (f:=fun j=>x j^3)
      (fun j _=>pow_nonneg (hx j) 3) (Finset.mem_univ top)
    simpa only [ht,upperComparisonShapeMean,normalizedUpperMean,x] using hs
  · calc
      _ = ∑ j,x j^3 := rfl
      _ ≤ ∑ j,(spectralRatio R hR)*x j^2 := by
        apply Finset.sum_le_sum
        intro j _
        have hh := mul_le_mul_of_nonneg_right (upperNormalizedSpectrum_le_ratio hR j) (sq_nonneg (x j))
        convert hh using 1 <;> dsimp [x] <;> ring
      _ = spectralRatio R hR := by rw [←Finset.mul_sum,h2,mul_one]

end
end SingularValueBounds.KL
