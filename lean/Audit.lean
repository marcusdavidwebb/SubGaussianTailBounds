import SingularValueBounds
import Lean.Util.CollectAxioms

/-!
Audit every KL theorem in the compiled environment and the retained shared
supporting targets. Reuse Lean's own transitive axiom collector with a shared
visited set: the union is contained in the allowlist precisely when every
individual target's dependency set is contained in it. No proof is supplied
or modified by this metaprogram.
-/
open Lean in
run_cmd do
  let env ← getEnv
  let current := env.constants.fold (fun acc name info =>
    if (`SingularValueBounds.KL).isPrefixOf name && info.isTheorem then name::acc else acc)
    ([] : List Name)
  let earlier : List Name := [
    `SingularValueBounds.quadraticFormEstimates_of_subGaussian,
    `SingularValueBounds.integral_ratio_cauchy,
    `SingularValueBounds.scalar_lower_exponential,
    `SingularValueBounds.scalar_upper_exponential,
    `SingularValueBounds.scalar_tail_second_moment,
    `SingularValueBounds.current_shift_mean_lower,
    `SingularValueBounds.current_shift_second_moment_upper,
    `SingularValueBounds.upperComparison_spectral,
    `SingularValueBounds.upperCriterion_determinant_bound,
    `SingularValueBounds.upperCriterion_posDef,
    `SingularValueBounds.upperShift_unique,
    `SingularValueBounds.upperShift_unique_preserves,
    `SingularValueBounds.spectralUpper_le_candidate,
    `SingularValueBounds.spectralUpper_gap,
    `SingularValueBounds.spectralLower_gap,
    `SingularValueBounds.spectralUpper_translate,
    `SingularValueBounds.spectralLower_translate,
    `SingularValueBounds.spectralUpper_zero,
    `SingularValueBounds.resolventRoot_unique,
    `SingularValueBounds.continuous_spectralUpper,
    `SingularValueBounds.continuous_spectralLower,
    `SingularValueBounds.independent_weighted_average,
    `SingularValueBounds.spectral_lower_sqrt_tail,
    `SingularValueBounds.spectral_upper_sqrt_tail]
  let targets := (current ++ earlier).toArray.qsort (fun a b => a.toString < b.toString)
  for name in targets do
    unless (env.checked.get.find? name).isSome do
      throwError "Audit target is absent from the checked kernel environment: {name}"
  let (_, state) := (((targets.toList.forM CollectAxioms.collect).run env).run {})
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for name in state.axioms do
    unless allowed.contains name do
      throwError "Unexpected axiom in the combined transitive dependencies: {name}"
  for name in targets do
    logInfo m!"AUDIT_TARGET {name}"
  logInfo m!"AUDIT_AXIOMS {state.axioms.toList}"
  logInfo m!"AUDIT_COMPLETE {targets.size} targets; {state.visited.size} visited constants"

#check SingularValueBounds.KL.weighted_entropy
#check SingularValueBounds.KL.weighted_entropy_of_nonneg
#check SingularValueBounds.KL.quadratic_exponential_det_bound
#check SingularValueBounds.KL.Certificates.exp_enclosure_of_certificate
#check SingularValueBounds.KL.Certificates.log_enclosure_of_certificate
#check SingularValueBounds.KL.quadratic_lower_laplace_general
#check SingularValueBounds.KL.quadratic_lower_laplace_one
#check SingularValueBounds.KL.TheoremKL
#check SingularValueBounds.KL.TheoremKLOne
#check SingularValueBounds.KL.HybridTarget
#check SingularValueBounds.KL.HybridEndpointTarget

-- Independently print the three final public results' transitive axioms.
#print axioms SingularValueBounds.KL.singular_value_tails_general_of_certificates
#print axioms SingularValueBounds.KL.singular_value_tails_one_of_certificates
#print axioms SingularValueBounds.KL.theorem_explicit_constants_of_certificates
#check SingularValueBounds.KL.singular_value_tails_general_of_certificates
#check SingularValueBounds.KL.singular_value_tails_one_of_certificates
#check SingularValueBounds.KL.theorem_explicit_constants_of_certificates
#print SingularValueBounds.KL.FinalCertificateConditions
