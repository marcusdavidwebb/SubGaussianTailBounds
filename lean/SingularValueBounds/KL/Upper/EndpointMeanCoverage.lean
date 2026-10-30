import SingularValueBounds.KL.Upper.EndpointMeanFinite

open Set
namespace SingularValueBounds.KL
open Certificates
noncomputable section
set_option maxHeartbeats 1500000

/-- Adjacent closed intervals cover their complete span; the left endpoint
may be made strict when the point lies above the first grid node. -/
theorem finite_grid_covers_Ioc (p : ℕ → ℝ) {n : ℕ} {a : ℝ}
    (ha : a∈Ioc (p 0) (p n)) :
    ∃i : ℕ,i<n ∧ a∈Ioc (p i) (p (i+1)) := by
  induction n with
  | zero => exact False.elim (not_lt_of_ge ha.2 ha.1)
  | succ n ih =>
    by_cases hn : a≤p n
    · obtain ⟨i,hi,ha'⟩ := ih ⟨ha.1,hn⟩
      exact ⟨i,by omega,ha'⟩
    · exact ⟨n,by omega,lt_of_not_ge hn,ha.2⟩

theorem endpoint_mean_joint_cover (h : EndpointMeanCertificateConditions)
    {a k : ℝ} (hk : k∈Icc (1/4 : ℝ) 1) (ha : k^3≤a ∧ a≤k) :
    ∃ki : Fin 60,∃ai : Fin 42,endpointMeanActive ki ai ∧
      (endpointMeanBox ki ai).contains a k := by
  obtain ⟨ki,hki,hkl,hkh⟩ : ∃ki : Fin 60,
      (if ki=0 then (1/4 : ℝ)≤k else ((ki.val+20 : ℝ)/80)<k) ∧
      ((ki.val+20 : ℝ)/80)≤k ∧ k≤((ki.val+21 : ℝ)/80) := by
    by_cases hk0 : k=(1/4 : ℝ)
    · exact ⟨0,by simp [hk0],by norm_num [hk0],by norm_num [hk0]⟩
    · have hk' : k∈Ioc (((0 : ℕ)+20 : ℝ)/80) (((60 : ℕ)+20 : ℝ)/80) := by
        norm_num
        exact ⟨lt_of_le_of_ne hk.1 (Ne.symm hk0),hk.2⟩
      obtain ⟨i,hi,hl,hr⟩ := finite_grid_covers_Ioc (fun i => (i+20 : ℝ)/80) hk'
      refine ⟨⟨i,hi⟩,?_,hl.le,?_⟩
      · split_ifs with he
        · exact hk.1
        · exact hl
      · push_cast at hr
        linarith
  let p : ℕ → ℝ := fun i => if hi : i<43 then (endpointMeanAPoint ⟨i,hi⟩ : ℝ) else 1
  have hp0 : p 0=0 := by simpa only [p,dif_pos (by omega : 0<43),Rat.cast_zero] using! congrArg (fun q : ℚ => (q : ℝ)) h.aGrid.1
  have hp42 : p 42=1 := by simpa only [p,dif_pos (by omega : 42<43),Rat.cast_one] using! congrArg (fun q : ℚ => (q : ℝ)) h.aGrid.2.1
  have ha0 : 0<a := (pow_pos (by linarith [hk.1] : 0<k) 3).trans_le ha.1
  have hap : a∈Ioc (p 0) (p 42) := by rw [hp0,hp42]; exact ⟨ha0,ha.2.trans hk.2⟩
  obtain ⟨j,hj,hal,hah⟩ := finite_grid_covers_Ioc p hap
  let ai : Fin 42 := ⟨j,hj⟩
  have hleft : (endpointMeanAPoint ⟨ai.val,by omega⟩ : ℝ)<a := by simpa [p,ai,show j<43 by omega] using hal
  have hright : a≤(endpointMeanAPoint ⟨ai.val+1,by omega⟩ : ℝ) := by simpa [p,ai,show j+1<43 by omega] using hah
  have hraw : (endpointMeanAPoint ⟨ai.val,by omega⟩ : ℝ)<endpointMeanAPoint ⟨ai.val+1,by omega⟩ := by exact_mod_cast h.aGrid.2.2 ai
  have hkCube : ((ki.val+20 : ℝ)/80)^3≤a := by
    have hk00 : (0 : ℝ)≤(ki.val+20 : ℝ)/80 := by positivity
    exact (pow_le_pow_left₀ hk00 hkl 3).trans ha.1
  have hStrictCube : ((ki.val+20 : ℝ)/80)^3<endpointMeanAPoint ⟨ai.val+1,by omega⟩ := by
    by_cases hki0 : ki=0
    · subst ki
      have hneq : (1/64 : ℝ)≠endpointMeanAPoint ⟨ai.val+1,by omega⟩ := by
        intro he
        apply h.quarterNondegenerate ai
        apply Rat.cast_injective (α := ℝ)
        norm_num
        exact he
      norm_num only [Fin.val_zero,Nat.cast_zero,zero_add] at hkCube ⊢
      exact lt_of_le_of_ne (hkCube.trans hright) hneq
    · have hstrict : ((ki.val+20 : ℝ)/80)<k := by simpa [hki0] using hki
      have hh := (pow_lt_pow_left₀ hstrict (by positivity : (0 : ℝ)≤(ki.val+20 : ℝ)/80) (by norm_num : 3≠0)).trans_le ha.1
      exact hh.trans_le hright
  have hContains : (endpointMeanBox ki ai).contains a k := by
    dsimp [endpointMeanBox,RationalBox.contains]
    push_cast
    exact ⟨⟨max_le hleft.le hkCube,hright⟩,hkl,hkh⟩
  refine ⟨ki,ai,?_,hContains⟩
  constructor
  · have hh : (max (endpointMeanAPoint ⟨ai.val,by omega⟩) (((ki.val+20 : ℚ)/80)^3) : ℚ)<
        endpointMeanAPoint ⟨ai.val+1,by omega⟩ := by
      have hhR : ((max (endpointMeanAPoint ⟨ai.val,by omega⟩) (((ki.val+20 : ℚ)/80)^3) : ℚ) : ℝ)<
          (endpointMeanAPoint ⟨ai.val+1,by omega⟩ : ℝ) := by
        push_cast
        exact max_lt hraw hStrictCube
      exact_mod_cast hhR
    exact hh
  · have hh := hContains.1.1.trans (ha.2.trans hkh)
    have hhR : ((endpointMeanBox ki ai).left : ℝ)≤((endpointMeanBox ki ai).top : ℝ) := by
      simpa only [endpointMeanBox,Rat.cast_div,Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat] using hh
    exact_mod_cast hhR

end
end SingularValueBounds.KL
