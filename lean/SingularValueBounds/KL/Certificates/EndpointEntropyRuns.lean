import Mathlib.Algebra.BigOperators.Intervals

/-! Exact decomposition of finite sums into contiguous rate runs. -/
namespace SingularValueBounds.KL.Certificates
open scoped BigOperators

structure EndpointRateRun where
  start : ℕ
  stop : ℕ
  rate : ℕ
  deriving DecidableEq, Repr

def EndpointRunsCover (start stop : ℕ) : List EndpointRateRun → Prop
  | [] => start = stop
  | r :: rs => r.start = start ∧ r.start ≤ r.stop ∧ EndpointRunsCover r.stop stop rs

def endpointRunsCoverDecidable (start stop : ℕ) (rs : List EndpointRateRun) :
    Decidable (EndpointRunsCover start stop rs) :=
  match rs with
  | [] => inferInstanceAs (Decidable (start = stop))
  | r :: rest =>
    letI := endpointRunsCoverDecidable r.stop stop rest
    inferInstanceAs
      (Decidable (r.start = start ∧ r.start ≤ r.stop ∧ EndpointRunsCover r.stop stop rest))

instance (start stop : ℕ) (rs : List EndpointRateRun) : Decidable (EndpointRunsCover start stop rs) :=
  endpointRunsCoverDecidable start stop rs

theorem EndpointRunsCover.le {start stop : ℕ} {rs : List EndpointRateRun}
    (h : EndpointRunsCover start stop rs) : start ≤ stop := by
  induction rs generalizing start with
  | nil => exact (show start = stop from h).le
  | cons r rest ih =>
    obtain ⟨hs, hr, hrest⟩ := h
    exact hs ▸ hr.trans (ih hrest)

theorem EndpointRunsCover.sum {M : Type*} [AddCommMonoid M]
    {start stop : ℕ} {rs : List EndpointRateRun}
    (h : EndpointRunsCover start stop rs) (f : ℕ → M) :
    (∑ j ∈ Finset.Ico start stop, f j) =
      (rs.map (fun r => ∑ j ∈ Finset.Ico r.start r.stop, f j)).sum := by
  induction rs generalizing start with
  | nil => simp [EndpointRunsCover] at h; simp [h]
  | cons r rest ih =>
    obtain ⟨hs, hr, hrest⟩ := h
    subst start
    rw [List.map_cons, List.sum_cons, ← ih hrest]
    exact (Finset.sum_Ico_consecutive f hr hrest.le).symm

def endpointRateOfRuns : List EndpointRateRun → ℕ → ℕ
  | [], _ => 90
  | r :: rs, j => if j < r.stop then r.rate else endpointRateOfRuns rs j

theorem EndpointRunsCover.start_le {start stop : ℕ} {rs : List EndpointRateRun}
    (h : EndpointRunsCover start stop rs) {r : EndpointRateRun} (hr : r ∈ rs) :
    start ≤ r.start := by
  induction rs generalizing start with
  | nil => simp at hr
  | cons first rest ih =>
    obtain ⟨hs, hfirst, hrest⟩ := h
    rcases List.mem_cons.mp hr with hsame | hr
    · subst r; exact hs.symm.le
    · exact hs ▸ hfirst.trans (ih hrest hr)

theorem EndpointRunsCover.rateOfRuns_eq {start stop : ℕ} {rs : List EndpointRateRun}
    (h : EndpointRunsCover start stop rs) {r : EndpointRateRun} (hr : r ∈ rs)
    {j : ℕ} (hj : j ∈ Finset.Ico r.start r.stop) : endpointRateOfRuns rs j = r.rate := by
  induction rs generalizing start with
  | nil => simp at hr
  | cons first rest ih =>
    obtain ⟨hs, hfirst, hrest⟩ := h
    rcases List.mem_cons.mp hr with hsame | hr
    · subst r
      simp only [endpointRateOfRuns, if_pos (Finset.mem_Ico.mp hj).2]
    · have hge := (hrest.start_le hr).trans (Finset.mem_Ico.mp hj).1
      rw [endpointRateOfRuns, if_neg (not_lt.mpr hge)]
      exact ih hrest hr

theorem EndpointRunsCover.exists_run {start stop : ℕ} {rs : List EndpointRateRun}
    (h : EndpointRunsCover start stop rs) {j : ℕ} (hj : j ∈ Finset.Ico start stop) :
    ∃ r ∈ rs, j ∈ Finset.Ico r.start r.stop := by
  induction rs generalizing start with
  | nil =>
    have he : start = stop := h
    simp [he] at hj
  | cons first rest ih =>
    obtain ⟨hs, hfirst, hrest⟩ := h
    by_cases hlt : j < first.stop
    · exact ⟨first, List.mem_cons_self, Finset.mem_Ico.mpr ⟨hs ▸ (Finset.mem_Ico.mp hj).1, hlt⟩⟩
    · obtain ⟨r, hr, hjr⟩ := ih hrest
        (Finset.mem_Ico.mpr ⟨not_lt.mp hlt, (Finset.mem_Ico.mp hj).2⟩)
      exact ⟨r, List.mem_cons_of_mem _ hr, hjr⟩

end SingularValueBounds.KL.Certificates
