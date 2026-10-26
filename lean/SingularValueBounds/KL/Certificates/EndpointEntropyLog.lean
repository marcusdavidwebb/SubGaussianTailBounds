import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block00
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block01
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block02
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block03
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block04
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block05
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block06
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block07
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block08
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block09
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block10
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block11
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block12
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block13
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block14
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block15
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block16
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block17
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block18
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block19
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block20
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block21
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block22
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block23
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block24
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block25
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block26
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block27
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block28
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block29
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block30
import SingularValueBounds.KL.Certificates.EndpointEntropyLogRows.Block31

/-! Every printed entropy-grid logarithm is equal to the checked integer table. -/
namespace SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem endpointLogGrid_eq (j : ℕ) (hj : 1 ≤ j) (hjEnd : j ≤ 8001) :
    logRoundedQ ((j:ℚ)/200) = (fixedQ (endpointLogLower j), fixedQ (endpointLogUpper j)) := by
  have hall (b : Fin 31) (i : Fin 256) :
      logRoundedQ (((256*b.val+i.val+1:ℕ):ℚ)/200) =
        (fixedQ (endpointLogLower (256*b.val+i.val+1)),
          fixedQ (endpointLogUpper (256*b.val+i.val+1))) := by
    fin_cases b
    · exact endpointLogGridBlock00 i
    · exact endpointLogGridBlock01 i
    · exact endpointLogGridBlock02 i
    · exact endpointLogGridBlock03 i
    · exact endpointLogGridBlock04 i
    · exact endpointLogGridBlock05 i
    · exact endpointLogGridBlock06 i
    · exact endpointLogGridBlock07 i
    · exact endpointLogGridBlock08 i
    · exact endpointLogGridBlock09 i
    · exact endpointLogGridBlock10 i
    · exact endpointLogGridBlock11 i
    · exact endpointLogGridBlock12 i
    · exact endpointLogGridBlock13 i
    · exact endpointLogGridBlock14 i
    · exact endpointLogGridBlock15 i
    · exact endpointLogGridBlock16 i
    · exact endpointLogGridBlock17 i
    · exact endpointLogGridBlock18 i
    · exact endpointLogGridBlock19 i
    · exact endpointLogGridBlock20 i
    · exact endpointLogGridBlock21 i
    · exact endpointLogGridBlock22 i
    · exact endpointLogGridBlock23 i
    · exact endpointLogGridBlock24 i
    · exact endpointLogGridBlock25 i
    · exact endpointLogGridBlock26 i
    · exact endpointLogGridBlock27 i
    · exact endpointLogGridBlock28 i
    · exact endpointLogGridBlock29 i
    · exact endpointLogGridBlock30 i
  by_cases h : j ≤ 7936
  · have he : 256*((j-1)/256)+(j-1)%256+1 = j := by omega
    simpa only [Fin.val_mk,he] using hall ⟨(j-1)/256,by omega⟩ ⟨(j-1)%256,by omega⟩
  · have he : 7936+(j-7937)+1 = j := by omega
    simpa only [Fin.val_mk,he] using endpointLogGridBlock31 ⟨j-7937,by omega⟩

private theorem logGridBounds00 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (0+i.val+1) ∧
      endpointLogUpper (0+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds01 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (256+i.val+1) ∧
      endpointLogUpper (256+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds02 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (512+i.val+1) ∧
      endpointLogUpper (512+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds03 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (768+i.val+1) ∧
      endpointLogUpper (768+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds04 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (1024+i.val+1) ∧
      endpointLogUpper (1024+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds05 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (1280+i.val+1) ∧
      endpointLogUpper (1280+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds06 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (1536+i.val+1) ∧
      endpointLogUpper (1536+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds07 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (1792+i.val+1) ∧
      endpointLogUpper (1792+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds08 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (2048+i.val+1) ∧
      endpointLogUpper (2048+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds09 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (2304+i.val+1) ∧
      endpointLogUpper (2304+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds10 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (2560+i.val+1) ∧
      endpointLogUpper (2560+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds11 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (2816+i.val+1) ∧
      endpointLogUpper (2816+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds12 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (3072+i.val+1) ∧
      endpointLogUpper (3072+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds13 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (3328+i.val+1) ∧
      endpointLogUpper (3328+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds14 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (3584+i.val+1) ∧
      endpointLogUpper (3584+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds15 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (3840+i.val+1) ∧
      endpointLogUpper (3840+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds16 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (4096+i.val+1) ∧
      endpointLogUpper (4096+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds17 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (4352+i.val+1) ∧
      endpointLogUpper (4352+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds18 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (4608+i.val+1) ∧
      endpointLogUpper (4608+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds19 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (4864+i.val+1) ∧
      endpointLogUpper (4864+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds20 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (5120+i.val+1) ∧
      endpointLogUpper (5120+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds21 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (5376+i.val+1) ∧
      endpointLogUpper (5376+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds22 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (5632+i.val+1) ∧
      endpointLogUpper (5632+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds23 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (5888+i.val+1) ∧
      endpointLogUpper (5888+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds24 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (6144+i.val+1) ∧
      endpointLogUpper (6144+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds25 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (6400+i.val+1) ∧
      endpointLogUpper (6400+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds26 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (6656+i.val+1) ∧
      endpointLogUpper (6656+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds27 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (6912+i.val+1) ∧
      endpointLogUpper (6912+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds28 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (7168+i.val+1) ∧
      endpointLogUpper (7168+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds29 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (7424+i.val+1) ∧
      endpointLogUpper (7424+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds30 : ∀ i : Fin 256,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (7680+i.val+1) ∧
      endpointLogUpper (7680+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

private theorem logGridBounds31 : ∀ i : Fin 65,
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (7936+i.val+1) ∧
      endpointLogUpper (7936+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by decide +kernel

theorem endpointLogGrid_bounds (j : ℕ) (hj : 1 ≤ j) (hjEnd : j ≤ 8001) :
    -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower j ∧ endpointLogUpper j ≤ 4*(fixedScaleNat:ℤ) := by
  have hall (b : Fin 31) (i : Fin 256) :
      -(6*(fixedScaleNat:ℤ)) ≤ endpointLogLower (256*b.val+i.val+1) ∧
        endpointLogUpper (256*b.val+i.val+1) ≤ 4*(fixedScaleNat:ℤ) := by
    fin_cases b
    · exact logGridBounds00 i
    · exact logGridBounds01 i
    · exact logGridBounds02 i
    · exact logGridBounds03 i
    · exact logGridBounds04 i
    · exact logGridBounds05 i
    · exact logGridBounds06 i
    · exact logGridBounds07 i
    · exact logGridBounds08 i
    · exact logGridBounds09 i
    · exact logGridBounds10 i
    · exact logGridBounds11 i
    · exact logGridBounds12 i
    · exact logGridBounds13 i
    · exact logGridBounds14 i
    · exact logGridBounds15 i
    · exact logGridBounds16 i
    · exact logGridBounds17 i
    · exact logGridBounds18 i
    · exact logGridBounds19 i
    · exact logGridBounds20 i
    · exact logGridBounds21 i
    · exact logGridBounds22 i
    · exact logGridBounds23 i
    · exact logGridBounds24 i
    · exact logGridBounds25 i
    · exact logGridBounds26 i
    · exact logGridBounds27 i
    · exact logGridBounds28 i
    · exact logGridBounds29 i
    · exact logGridBounds30 i
  by_cases h : j ≤ 7936
  · have he : 256*((j-1)/256)+(j-1)%256+1 = j := by omega
    simpa only [Fin.val_mk,he] using hall ⟨(j-1)/256,by omega⟩ ⟨(j-1)%256,by omega⟩
  · have he : 7936+(j-7937)+1 = j := by omega
    simpa only [Fin.val_mk,he] using logGridBounds31 ⟨j-7937,by omega⟩

end SingularValueBounds.KL.Certificates
