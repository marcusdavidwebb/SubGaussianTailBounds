import SingularValueBounds.KL.Certificates.EndpointEntropyDecayRows.Block00
import SingularValueBounds.KL.Certificates.EndpointEntropyDecayRows.Block01
import SingularValueBounds.KL.Certificates.EndpointEntropyDecayRows.Block02
import SingularValueBounds.KL.Certificates.EndpointEntropyDecayRows.Block03
import SingularValueBounds.KL.Certificates.EndpointEntropyDecayRows.Block04
import SingularValueBounds.KL.Certificates.EndpointEntropyDecayRows.Block05
import SingularValueBounds.KL.Certificates.EndpointEntropyDecayRows.Block06
import SingularValueBounds.KL.Certificates.EndpointEntropyDecayRows.Block07
import SingularValueBounds.KL.Certificates.EndpointEntropyDecayRows.Block08
import SingularValueBounds.KL.Certificates.EndpointEntropyDecayRows.Block09
import SingularValueBounds.KL.Certificates.EndpointEntropyDecayRows.Block10
import SingularValueBounds.KL.Certificates.EndpointEntropyDecayRows.Block11

/-! Shared exact decay sequences and weighted prefix sums for every printed rate. -/
namespace SingularValueBounds.KL.Certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def endpointDecayBases : EntropyLookup ℤ :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf endpointDecayBase90) (.leaf endpointDecayBase154)) (.branch (.leaf endpointDecayBase122) (.leaf endpointDecayBase186))) (.branch (.branch (.leaf endpointDecayBase106) (.leaf endpointDecayBase170)) (.branch (.leaf endpointDecayBase138) (.leaf endpointDecayBase90)))) (.branch (.branch (.branch (.leaf endpointDecayBase98) (.leaf endpointDecayBase162)) (.branch (.leaf endpointDecayBase130) (.leaf endpointDecayBase194))) (.branch (.branch (.leaf endpointDecayBase114) (.leaf endpointDecayBase178)) (.branch (.leaf endpointDecayBase146) (.leaf endpointDecayBase90))))) (.branch (.branch (.branch (.branch (.leaf endpointDecayBase94) (.leaf endpointDecayBase158)) (.branch (.leaf endpointDecayBase126) (.leaf endpointDecayBase190))) (.branch (.branch (.leaf endpointDecayBase110) (.leaf endpointDecayBase174)) (.branch (.leaf endpointDecayBase142) (.leaf endpointDecayBase90)))) (.branch (.branch (.branch (.leaf endpointDecayBase102) (.leaf endpointDecayBase166)) (.branch (.leaf endpointDecayBase134) (.leaf endpointDecayBase198))) (.branch (.branch (.leaf endpointDecayBase118) (.leaf endpointDecayBase182)) (.branch (.leaf endpointDecayBase150) (.leaf endpointDecayBase90)))))) (.branch (.branch (.branch (.branch (.branch (.leaf endpointDecayBase92) (.leaf endpointDecayBase156)) (.branch (.leaf endpointDecayBase124) (.leaf endpointDecayBase188))) (.branch (.branch (.leaf endpointDecayBase108) (.leaf endpointDecayBase172)) (.branch (.leaf endpointDecayBase140) (.leaf endpointDecayBase90)))) (.branch (.branch (.branch (.leaf endpointDecayBase100) (.leaf endpointDecayBase164)) (.branch (.leaf endpointDecayBase132) (.leaf endpointDecayBase196))) (.branch (.branch (.leaf endpointDecayBase116) (.leaf endpointDecayBase180)) (.branch (.leaf endpointDecayBase148) (.leaf endpointDecayBase90))))) (.branch (.branch (.branch (.branch (.leaf endpointDecayBase96) (.leaf endpointDecayBase160)) (.branch (.leaf endpointDecayBase128) (.leaf endpointDecayBase192))) (.branch (.branch (.leaf endpointDecayBase112) (.leaf endpointDecayBase176)) (.branch (.leaf endpointDecayBase144) (.leaf endpointDecayBase90)))) (.branch (.branch (.branch (.leaf endpointDecayBase104) (.leaf endpointDecayBase168)) (.branch (.leaf endpointDecayBase136) (.leaf endpointDecayBase200))) (.branch (.branch (.leaf endpointDecayBase120) (.leaf endpointDecayBase184)) (.branch (.leaf endpointDecayBase152) (.leaf endpointDecayBase90))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf endpointDecayBase91) (.leaf endpointDecayBase155)) (.branch (.leaf endpointDecayBase123) (.leaf endpointDecayBase187))) (.branch (.branch (.leaf endpointDecayBase107) (.leaf endpointDecayBase171)) (.branch (.leaf endpointDecayBase139) (.leaf endpointDecayBase90)))) (.branch (.branch (.branch (.leaf endpointDecayBase99) (.leaf endpointDecayBase163)) (.branch (.leaf endpointDecayBase131) (.leaf endpointDecayBase195))) (.branch (.branch (.leaf endpointDecayBase115) (.leaf endpointDecayBase179)) (.branch (.leaf endpointDecayBase147) (.leaf endpointDecayBase90))))) (.branch (.branch (.branch (.branch (.leaf endpointDecayBase95) (.leaf endpointDecayBase159)) (.branch (.leaf endpointDecayBase127) (.leaf endpointDecayBase191))) (.branch (.branch (.leaf endpointDecayBase111) (.leaf endpointDecayBase175)) (.branch (.leaf endpointDecayBase143) (.leaf endpointDecayBase90)))) (.branch (.branch (.branch (.leaf endpointDecayBase103) (.leaf endpointDecayBase167)) (.branch (.leaf endpointDecayBase135) (.leaf endpointDecayBase199))) (.branch (.branch (.leaf endpointDecayBase119) (.leaf endpointDecayBase183)) (.branch (.leaf endpointDecayBase151) (.leaf endpointDecayBase90)))))) (.branch (.branch (.branch (.branch (.branch (.leaf endpointDecayBase93) (.leaf endpointDecayBase157)) (.branch (.leaf endpointDecayBase125) (.leaf endpointDecayBase189))) (.branch (.branch (.leaf endpointDecayBase109) (.leaf endpointDecayBase173)) (.branch (.leaf endpointDecayBase141) (.leaf endpointDecayBase90)))) (.branch (.branch (.branch (.leaf endpointDecayBase101) (.leaf endpointDecayBase165)) (.branch (.leaf endpointDecayBase133) (.leaf endpointDecayBase197))) (.branch (.branch (.leaf endpointDecayBase117) (.leaf endpointDecayBase181)) (.branch (.leaf endpointDecayBase149) (.leaf endpointDecayBase90))))) (.branch (.branch (.branch (.branch (.leaf endpointDecayBase97) (.leaf endpointDecayBase161)) (.branch (.leaf endpointDecayBase129) (.leaf endpointDecayBase193))) (.branch (.branch (.leaf endpointDecayBase113) (.leaf endpointDecayBase177)) (.branch (.leaf endpointDecayBase145) (.leaf endpointDecayBase90)))) (.branch (.branch (.branch (.leaf endpointDecayBase105) (.leaf endpointDecayBase169)) (.branch (.leaf endpointDecayBase137) (.leaf endpointDecayBase90))) (.branch (.branch (.leaf endpointDecayBase121) (.leaf endpointDecayBase185)) (.branch (.leaf endpointDecayBase153) (.leaf endpointDecayBase90))))))))

noncomputable def endpointDecayCheckpoints : EntropyLookup (EntropyLookup EndpointEntropyState) :=
(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.leaf endpointDecayCheckpoints90) (.leaf endpointDecayCheckpoints154)) (.branch (.leaf endpointDecayCheckpoints122) (.leaf endpointDecayCheckpoints186))) (.branch (.branch (.leaf endpointDecayCheckpoints106) (.leaf endpointDecayCheckpoints170)) (.branch (.leaf endpointDecayCheckpoints138) (.leaf endpointDecayCheckpoints90)))) (.branch (.branch (.branch (.leaf endpointDecayCheckpoints98) (.leaf endpointDecayCheckpoints162)) (.branch (.leaf endpointDecayCheckpoints130) (.leaf endpointDecayCheckpoints194))) (.branch (.branch (.leaf endpointDecayCheckpoints114) (.leaf endpointDecayCheckpoints178)) (.branch (.leaf endpointDecayCheckpoints146) (.leaf endpointDecayCheckpoints90))))) (.branch (.branch (.branch (.branch (.leaf endpointDecayCheckpoints94) (.leaf endpointDecayCheckpoints158)) (.branch (.leaf endpointDecayCheckpoints126) (.leaf endpointDecayCheckpoints190))) (.branch (.branch (.leaf endpointDecayCheckpoints110) (.leaf endpointDecayCheckpoints174)) (.branch (.leaf endpointDecayCheckpoints142) (.leaf endpointDecayCheckpoints90)))) (.branch (.branch (.branch (.leaf endpointDecayCheckpoints102) (.leaf endpointDecayCheckpoints166)) (.branch (.leaf endpointDecayCheckpoints134) (.leaf endpointDecayCheckpoints198))) (.branch (.branch (.leaf endpointDecayCheckpoints118) (.leaf endpointDecayCheckpoints182)) (.branch (.leaf endpointDecayCheckpoints150) (.leaf endpointDecayCheckpoints90)))))) (.branch (.branch (.branch (.branch (.branch (.leaf endpointDecayCheckpoints92) (.leaf endpointDecayCheckpoints156)) (.branch (.leaf endpointDecayCheckpoints124) (.leaf endpointDecayCheckpoints188))) (.branch (.branch (.leaf endpointDecayCheckpoints108) (.leaf endpointDecayCheckpoints172)) (.branch (.leaf endpointDecayCheckpoints140) (.leaf endpointDecayCheckpoints90)))) (.branch (.branch (.branch (.leaf endpointDecayCheckpoints100) (.leaf endpointDecayCheckpoints164)) (.branch (.leaf endpointDecayCheckpoints132) (.leaf endpointDecayCheckpoints196))) (.branch (.branch (.leaf endpointDecayCheckpoints116) (.leaf endpointDecayCheckpoints180)) (.branch (.leaf endpointDecayCheckpoints148) (.leaf endpointDecayCheckpoints90))))) (.branch (.branch (.branch (.branch (.leaf endpointDecayCheckpoints96) (.leaf endpointDecayCheckpoints160)) (.branch (.leaf endpointDecayCheckpoints128) (.leaf endpointDecayCheckpoints192))) (.branch (.branch (.leaf endpointDecayCheckpoints112) (.leaf endpointDecayCheckpoints176)) (.branch (.leaf endpointDecayCheckpoints144) (.leaf endpointDecayCheckpoints90)))) (.branch (.branch (.branch (.leaf endpointDecayCheckpoints104) (.leaf endpointDecayCheckpoints168)) (.branch (.leaf endpointDecayCheckpoints136) (.leaf endpointDecayCheckpoints200))) (.branch (.branch (.leaf endpointDecayCheckpoints120) (.leaf endpointDecayCheckpoints184)) (.branch (.leaf endpointDecayCheckpoints152) (.leaf endpointDecayCheckpoints90))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.leaf endpointDecayCheckpoints91) (.leaf endpointDecayCheckpoints155)) (.branch (.leaf endpointDecayCheckpoints123) (.leaf endpointDecayCheckpoints187))) (.branch (.branch (.leaf endpointDecayCheckpoints107) (.leaf endpointDecayCheckpoints171)) (.branch (.leaf endpointDecayCheckpoints139) (.leaf endpointDecayCheckpoints90)))) (.branch (.branch (.branch (.leaf endpointDecayCheckpoints99) (.leaf endpointDecayCheckpoints163)) (.branch (.leaf endpointDecayCheckpoints131) (.leaf endpointDecayCheckpoints195))) (.branch (.branch (.leaf endpointDecayCheckpoints115) (.leaf endpointDecayCheckpoints179)) (.branch (.leaf endpointDecayCheckpoints147) (.leaf endpointDecayCheckpoints90))))) (.branch (.branch (.branch (.branch (.leaf endpointDecayCheckpoints95) (.leaf endpointDecayCheckpoints159)) (.branch (.leaf endpointDecayCheckpoints127) (.leaf endpointDecayCheckpoints191))) (.branch (.branch (.leaf endpointDecayCheckpoints111) (.leaf endpointDecayCheckpoints175)) (.branch (.leaf endpointDecayCheckpoints143) (.leaf endpointDecayCheckpoints90)))) (.branch (.branch (.branch (.leaf endpointDecayCheckpoints103) (.leaf endpointDecayCheckpoints167)) (.branch (.leaf endpointDecayCheckpoints135) (.leaf endpointDecayCheckpoints199))) (.branch (.branch (.leaf endpointDecayCheckpoints119) (.leaf endpointDecayCheckpoints183)) (.branch (.leaf endpointDecayCheckpoints151) (.leaf endpointDecayCheckpoints90)))))) (.branch (.branch (.branch (.branch (.branch (.leaf endpointDecayCheckpoints93) (.leaf endpointDecayCheckpoints157)) (.branch (.leaf endpointDecayCheckpoints125) (.leaf endpointDecayCheckpoints189))) (.branch (.branch (.leaf endpointDecayCheckpoints109) (.leaf endpointDecayCheckpoints173)) (.branch (.leaf endpointDecayCheckpoints141) (.leaf endpointDecayCheckpoints90)))) (.branch (.branch (.branch (.leaf endpointDecayCheckpoints101) (.leaf endpointDecayCheckpoints165)) (.branch (.leaf endpointDecayCheckpoints133) (.leaf endpointDecayCheckpoints197))) (.branch (.branch (.leaf endpointDecayCheckpoints117) (.leaf endpointDecayCheckpoints181)) (.branch (.leaf endpointDecayCheckpoints149) (.leaf endpointDecayCheckpoints90))))) (.branch (.branch (.branch (.branch (.leaf endpointDecayCheckpoints97) (.leaf endpointDecayCheckpoints161)) (.branch (.leaf endpointDecayCheckpoints129) (.leaf endpointDecayCheckpoints193))) (.branch (.branch (.leaf endpointDecayCheckpoints113) (.leaf endpointDecayCheckpoints177)) (.branch (.leaf endpointDecayCheckpoints145) (.leaf endpointDecayCheckpoints90)))) (.branch (.branch (.branch (.leaf endpointDecayCheckpoints105) (.leaf endpointDecayCheckpoints169)) (.branch (.leaf endpointDecayCheckpoints137) (.leaf endpointDecayCheckpoints90))) (.branch (.branch (.leaf endpointDecayCheckpoints121) (.leaf endpointDecayCheckpoints185)) (.branch (.leaf endpointDecayCheckpoints153) (.leaf endpointDecayCheckpoints90))))))))

noncomputable def endpointDecayBaseInteger (q : ℕ) : ℤ := endpointDecayBases.get (q-90)
noncomputable def endpointDecayCheckpoint (q j : ℕ) : EndpointEntropyState :=
  (endpointDecayCheckpoints.get (q-90)).get j

noncomputable def endpointDecayState (q j : ℕ) : EndpointEntropyState :=
  endpointEntropyCached (endpointDecayBaseInteger q) endpointLogUpper (endpointDecayCheckpoint q) j

theorem endpointDecayBase_eq (q : ℕ) (hlo : 90 ≤ q) (hhi : q ≤ 200) :
    endpointDecayBaseQ q = fixedQ (endpointDecayBaseInteger q) := by
  have hall (i : Fin 111) : endpointDecayBaseQ (90+i.val) =
      fixedQ (endpointDecayBaseInteger (90+i.val)) := by
    fin_cases i
    · exact endpointDecayBase90_eq
    · exact endpointDecayBase91_eq
    · exact endpointDecayBase92_eq
    · exact endpointDecayBase93_eq
    · exact endpointDecayBase94_eq
    · exact endpointDecayBase95_eq
    · exact endpointDecayBase96_eq
    · exact endpointDecayBase97_eq
    · exact endpointDecayBase98_eq
    · exact endpointDecayBase99_eq
    · exact endpointDecayBase100_eq
    · exact endpointDecayBase101_eq
    · exact endpointDecayBase102_eq
    · exact endpointDecayBase103_eq
    · exact endpointDecayBase104_eq
    · exact endpointDecayBase105_eq
    · exact endpointDecayBase106_eq
    · exact endpointDecayBase107_eq
    · exact endpointDecayBase108_eq
    · exact endpointDecayBase109_eq
    · exact endpointDecayBase110_eq
    · exact endpointDecayBase111_eq
    · exact endpointDecayBase112_eq
    · exact endpointDecayBase113_eq
    · exact endpointDecayBase114_eq
    · exact endpointDecayBase115_eq
    · exact endpointDecayBase116_eq
    · exact endpointDecayBase117_eq
    · exact endpointDecayBase118_eq
    · exact endpointDecayBase119_eq
    · exact endpointDecayBase120_eq
    · exact endpointDecayBase121_eq
    · exact endpointDecayBase122_eq
    · exact endpointDecayBase123_eq
    · exact endpointDecayBase124_eq
    · exact endpointDecayBase125_eq
    · exact endpointDecayBase126_eq
    · exact endpointDecayBase127_eq
    · exact endpointDecayBase128_eq
    · exact endpointDecayBase129_eq
    · exact endpointDecayBase130_eq
    · exact endpointDecayBase131_eq
    · exact endpointDecayBase132_eq
    · exact endpointDecayBase133_eq
    · exact endpointDecayBase134_eq
    · exact endpointDecayBase135_eq
    · exact endpointDecayBase136_eq
    · exact endpointDecayBase137_eq
    · exact endpointDecayBase138_eq
    · exact endpointDecayBase139_eq
    · exact endpointDecayBase140_eq
    · exact endpointDecayBase141_eq
    · exact endpointDecayBase142_eq
    · exact endpointDecayBase143_eq
    · exact endpointDecayBase144_eq
    · exact endpointDecayBase145_eq
    · exact endpointDecayBase146_eq
    · exact endpointDecayBase147_eq
    · exact endpointDecayBase148_eq
    · exact endpointDecayBase149_eq
    · exact endpointDecayBase150_eq
    · exact endpointDecayBase151_eq
    · exact endpointDecayBase152_eq
    · exact endpointDecayBase153_eq
    · exact endpointDecayBase154_eq
    · exact endpointDecayBase155_eq
    · exact endpointDecayBase156_eq
    · exact endpointDecayBase157_eq
    · exact endpointDecayBase158_eq
    · exact endpointDecayBase159_eq
    · exact endpointDecayBase160_eq
    · exact endpointDecayBase161_eq
    · exact endpointDecayBase162_eq
    · exact endpointDecayBase163_eq
    · exact endpointDecayBase164_eq
    · exact endpointDecayBase165_eq
    · exact endpointDecayBase166_eq
    · exact endpointDecayBase167_eq
    · exact endpointDecayBase168_eq
    · exact endpointDecayBase169_eq
    · exact endpointDecayBase170_eq
    · exact endpointDecayBase171_eq
    · exact endpointDecayBase172_eq
    · exact endpointDecayBase173_eq
    · exact endpointDecayBase174_eq
    · exact endpointDecayBase175_eq
    · exact endpointDecayBase176_eq
    · exact endpointDecayBase177_eq
    · exact endpointDecayBase178_eq
    · exact endpointDecayBase179_eq
    · exact endpointDecayBase180_eq
    · exact endpointDecayBase181_eq
    · exact endpointDecayBase182_eq
    · exact endpointDecayBase183_eq
    · exact endpointDecayBase184_eq
    · exact endpointDecayBase185_eq
    · exact endpointDecayBase186_eq
    · exact endpointDecayBase187_eq
    · exact endpointDecayBase188_eq
    · exact endpointDecayBase189_eq
    · exact endpointDecayBase190_eq
    · exact endpointDecayBase191_eq
    · exact endpointDecayBase192_eq
    · exact endpointDecayBase193_eq
    · exact endpointDecayBase194_eq
    · exact endpointDecayBase195_eq
    · exact endpointDecayBase196_eq
    · exact endpointDecayBase197_eq
    · exact endpointDecayBase198_eq
    · exact endpointDecayBase199_eq
    · exact endpointDecayBase200_eq
  have he : 90+(q-90) = q := by omega
  simpa only [Fin.val_mk,he] using hall ⟨q-90,by omega⟩

theorem endpointDecayCheckpoint_zero (q : ℕ) (hlo : 90 ≤ q) (hhi : q ≤ 200) :
    endpointDecayCheckpoint q 0 = endpointEntropyInitial := by
  have hall (i : Fin 111) : endpointDecayCheckpoint (90+i.val) 0 = endpointEntropyInitial := by
    fin_cases i
    · exact endpointDecayCheckpoints90_zero
    · exact endpointDecayCheckpoints91_zero
    · exact endpointDecayCheckpoints92_zero
    · exact endpointDecayCheckpoints93_zero
    · exact endpointDecayCheckpoints94_zero
    · exact endpointDecayCheckpoints95_zero
    · exact endpointDecayCheckpoints96_zero
    · exact endpointDecayCheckpoints97_zero
    · exact endpointDecayCheckpoints98_zero
    · exact endpointDecayCheckpoints99_zero
    · exact endpointDecayCheckpoints100_zero
    · exact endpointDecayCheckpoints101_zero
    · exact endpointDecayCheckpoints102_zero
    · exact endpointDecayCheckpoints103_zero
    · exact endpointDecayCheckpoints104_zero
    · exact endpointDecayCheckpoints105_zero
    · exact endpointDecayCheckpoints106_zero
    · exact endpointDecayCheckpoints107_zero
    · exact endpointDecayCheckpoints108_zero
    · exact endpointDecayCheckpoints109_zero
    · exact endpointDecayCheckpoints110_zero
    · exact endpointDecayCheckpoints111_zero
    · exact endpointDecayCheckpoints112_zero
    · exact endpointDecayCheckpoints113_zero
    · exact endpointDecayCheckpoints114_zero
    · exact endpointDecayCheckpoints115_zero
    · exact endpointDecayCheckpoints116_zero
    · exact endpointDecayCheckpoints117_zero
    · exact endpointDecayCheckpoints118_zero
    · exact endpointDecayCheckpoints119_zero
    · exact endpointDecayCheckpoints120_zero
    · exact endpointDecayCheckpoints121_zero
    · exact endpointDecayCheckpoints122_zero
    · exact endpointDecayCheckpoints123_zero
    · exact endpointDecayCheckpoints124_zero
    · exact endpointDecayCheckpoints125_zero
    · exact endpointDecayCheckpoints126_zero
    · exact endpointDecayCheckpoints127_zero
    · exact endpointDecayCheckpoints128_zero
    · exact endpointDecayCheckpoints129_zero
    · exact endpointDecayCheckpoints130_zero
    · exact endpointDecayCheckpoints131_zero
    · exact endpointDecayCheckpoints132_zero
    · exact endpointDecayCheckpoints133_zero
    · exact endpointDecayCheckpoints134_zero
    · exact endpointDecayCheckpoints135_zero
    · exact endpointDecayCheckpoints136_zero
    · exact endpointDecayCheckpoints137_zero
    · exact endpointDecayCheckpoints138_zero
    · exact endpointDecayCheckpoints139_zero
    · exact endpointDecayCheckpoints140_zero
    · exact endpointDecayCheckpoints141_zero
    · exact endpointDecayCheckpoints142_zero
    · exact endpointDecayCheckpoints143_zero
    · exact endpointDecayCheckpoints144_zero
    · exact endpointDecayCheckpoints145_zero
    · exact endpointDecayCheckpoints146_zero
    · exact endpointDecayCheckpoints147_zero
    · exact endpointDecayCheckpoints148_zero
    · exact endpointDecayCheckpoints149_zero
    · exact endpointDecayCheckpoints150_zero
    · exact endpointDecayCheckpoints151_zero
    · exact endpointDecayCheckpoints152_zero
    · exact endpointDecayCheckpoints153_zero
    · exact endpointDecayCheckpoints154_zero
    · exact endpointDecayCheckpoints155_zero
    · exact endpointDecayCheckpoints156_zero
    · exact endpointDecayCheckpoints157_zero
    · exact endpointDecayCheckpoints158_zero
    · exact endpointDecayCheckpoints159_zero
    · exact endpointDecayCheckpoints160_zero
    · exact endpointDecayCheckpoints161_zero
    · exact endpointDecayCheckpoints162_zero
    · exact endpointDecayCheckpoints163_zero
    · exact endpointDecayCheckpoints164_zero
    · exact endpointDecayCheckpoints165_zero
    · exact endpointDecayCheckpoints166_zero
    · exact endpointDecayCheckpoints167_zero
    · exact endpointDecayCheckpoints168_zero
    · exact endpointDecayCheckpoints169_zero
    · exact endpointDecayCheckpoints170_zero
    · exact endpointDecayCheckpoints171_zero
    · exact endpointDecayCheckpoints172_zero
    · exact endpointDecayCheckpoints173_zero
    · exact endpointDecayCheckpoints174_zero
    · exact endpointDecayCheckpoints175_zero
    · exact endpointDecayCheckpoints176_zero
    · exact endpointDecayCheckpoints177_zero
    · exact endpointDecayCheckpoints178_zero
    · exact endpointDecayCheckpoints179_zero
    · exact endpointDecayCheckpoints180_zero
    · exact endpointDecayCheckpoints181_zero
    · exact endpointDecayCheckpoints182_zero
    · exact endpointDecayCheckpoints183_zero
    · exact endpointDecayCheckpoints184_zero
    · exact endpointDecayCheckpoints185_zero
    · exact endpointDecayCheckpoints186_zero
    · exact endpointDecayCheckpoints187_zero
    · exact endpointDecayCheckpoints188_zero
    · exact endpointDecayCheckpoints189_zero
    · exact endpointDecayCheckpoints190_zero
    · exact endpointDecayCheckpoints191_zero
    · exact endpointDecayCheckpoints192_zero
    · exact endpointDecayCheckpoints193_zero
    · exact endpointDecayCheckpoints194_zero
    · exact endpointDecayCheckpoints195_zero
    · exact endpointDecayCheckpoints196_zero
    · exact endpointDecayCheckpoints197_zero
    · exact endpointDecayCheckpoints198_zero
    · exact endpointDecayCheckpoints199_zero
    · exact endpointDecayCheckpoints200_zero
  have he : 90+(q-90) = q := by omega
  simpa only [Fin.val_mk,he] using hall ⟨q-90,by omega⟩

theorem endpointDecayCheckpoint_step (q i : ℕ) (hlo : 90 ≤ q) (hhi : q ≤ 200)
    (hi : i < 250) :
    endpointDecayCheckpoint q (i+1) =
      endpointEntropyRun (endpointDecayBaseInteger q) endpointLogUpper (32*i) 32
        (endpointDecayCheckpoint q i) := by
  have hall (r : Fin 111) (j : Fin 250) :
      endpointDecayCheckpoint (90+r.val) (j.val+1) =
        endpointEntropyRun (endpointDecayBaseInteger (90+r.val)) endpointLogUpper (32*j.val) 32
          (endpointDecayCheckpoint (90+r.val) j.val) := by
    fin_cases r
    · exact endpointDecayCheckpoints90_step j
    · exact endpointDecayCheckpoints91_step j
    · exact endpointDecayCheckpoints92_step j
    · exact endpointDecayCheckpoints93_step j
    · exact endpointDecayCheckpoints94_step j
    · exact endpointDecayCheckpoints95_step j
    · exact endpointDecayCheckpoints96_step j
    · exact endpointDecayCheckpoints97_step j
    · exact endpointDecayCheckpoints98_step j
    · exact endpointDecayCheckpoints99_step j
    · exact endpointDecayCheckpoints100_step j
    · exact endpointDecayCheckpoints101_step j
    · exact endpointDecayCheckpoints102_step j
    · exact endpointDecayCheckpoints103_step j
    · exact endpointDecayCheckpoints104_step j
    · exact endpointDecayCheckpoints105_step j
    · exact endpointDecayCheckpoints106_step j
    · exact endpointDecayCheckpoints107_step j
    · exact endpointDecayCheckpoints108_step j
    · exact endpointDecayCheckpoints109_step j
    · exact endpointDecayCheckpoints110_step j
    · exact endpointDecayCheckpoints111_step j
    · exact endpointDecayCheckpoints112_step j
    · exact endpointDecayCheckpoints113_step j
    · exact endpointDecayCheckpoints114_step j
    · exact endpointDecayCheckpoints115_step j
    · exact endpointDecayCheckpoints116_step j
    · exact endpointDecayCheckpoints117_step j
    · exact endpointDecayCheckpoints118_step j
    · exact endpointDecayCheckpoints119_step j
    · exact endpointDecayCheckpoints120_step j
    · exact endpointDecayCheckpoints121_step j
    · exact endpointDecayCheckpoints122_step j
    · exact endpointDecayCheckpoints123_step j
    · exact endpointDecayCheckpoints124_step j
    · exact endpointDecayCheckpoints125_step j
    · exact endpointDecayCheckpoints126_step j
    · exact endpointDecayCheckpoints127_step j
    · exact endpointDecayCheckpoints128_step j
    · exact endpointDecayCheckpoints129_step j
    · exact endpointDecayCheckpoints130_step j
    · exact endpointDecayCheckpoints131_step j
    · exact endpointDecayCheckpoints132_step j
    · exact endpointDecayCheckpoints133_step j
    · exact endpointDecayCheckpoints134_step j
    · exact endpointDecayCheckpoints135_step j
    · exact endpointDecayCheckpoints136_step j
    · exact endpointDecayCheckpoints137_step j
    · exact endpointDecayCheckpoints138_step j
    · exact endpointDecayCheckpoints139_step j
    · exact endpointDecayCheckpoints140_step j
    · exact endpointDecayCheckpoints141_step j
    · exact endpointDecayCheckpoints142_step j
    · exact endpointDecayCheckpoints143_step j
    · exact endpointDecayCheckpoints144_step j
    · exact endpointDecayCheckpoints145_step j
    · exact endpointDecayCheckpoints146_step j
    · exact endpointDecayCheckpoints147_step j
    · exact endpointDecayCheckpoints148_step j
    · exact endpointDecayCheckpoints149_step j
    · exact endpointDecayCheckpoints150_step j
    · exact endpointDecayCheckpoints151_step j
    · exact endpointDecayCheckpoints152_step j
    · exact endpointDecayCheckpoints153_step j
    · exact endpointDecayCheckpoints154_step j
    · exact endpointDecayCheckpoints155_step j
    · exact endpointDecayCheckpoints156_step j
    · exact endpointDecayCheckpoints157_step j
    · exact endpointDecayCheckpoints158_step j
    · exact endpointDecayCheckpoints159_step j
    · exact endpointDecayCheckpoints160_step j
    · exact endpointDecayCheckpoints161_step j
    · exact endpointDecayCheckpoints162_step j
    · exact endpointDecayCheckpoints163_step j
    · exact endpointDecayCheckpoints164_step j
    · exact endpointDecayCheckpoints165_step j
    · exact endpointDecayCheckpoints166_step j
    · exact endpointDecayCheckpoints167_step j
    · exact endpointDecayCheckpoints168_step j
    · exact endpointDecayCheckpoints169_step j
    · exact endpointDecayCheckpoints170_step j
    · exact endpointDecayCheckpoints171_step j
    · exact endpointDecayCheckpoints172_step j
    · exact endpointDecayCheckpoints173_step j
    · exact endpointDecayCheckpoints174_step j
    · exact endpointDecayCheckpoints175_step j
    · exact endpointDecayCheckpoints176_step j
    · exact endpointDecayCheckpoints177_step j
    · exact endpointDecayCheckpoints178_step j
    · exact endpointDecayCheckpoints179_step j
    · exact endpointDecayCheckpoints180_step j
    · exact endpointDecayCheckpoints181_step j
    · exact endpointDecayCheckpoints182_step j
    · exact endpointDecayCheckpoints183_step j
    · exact endpointDecayCheckpoints184_step j
    · exact endpointDecayCheckpoints185_step j
    · exact endpointDecayCheckpoints186_step j
    · exact endpointDecayCheckpoints187_step j
    · exact endpointDecayCheckpoints188_step j
    · exact endpointDecayCheckpoints189_step j
    · exact endpointDecayCheckpoints190_step j
    · exact endpointDecayCheckpoints191_step j
    · exact endpointDecayCheckpoints192_step j
    · exact endpointDecayCheckpoints193_step j
    · exact endpointDecayCheckpoints194_step j
    · exact endpointDecayCheckpoints195_step j
    · exact endpointDecayCheckpoints196_step j
    · exact endpointDecayCheckpoints197_step j
    · exact endpointDecayCheckpoints198_step j
    · exact endpointDecayCheckpoints199_step j
    · exact endpointDecayCheckpoints200_step j
  have he : 90+(q-90) = q := by omega
  simpa only [Fin.val_mk,he] using hall ⟨q-90,by omega⟩ ⟨i,hi⟩

theorem endpointDecayState_correct (q j : ℕ) (hlo : 90 ≤ q) (hhi : q ≤ 200)
    (hj : j ≤ 8000) :
    endpointDecayState q j = endpointEntropyState (endpointDecayBaseInteger q) endpointLogUpper j :=
  endpointEntropyCached_correct _ _ _ 250 j (endpointDecayCheckpoint_zero q hlo hhi)
    (fun i hi => endpointDecayCheckpoint_step q i hlo hhi hi) (by omega)

theorem endpointDecay_eq (q j : ℕ) (hlo : 90 ≤ q) (hhi : q ≤ 200) (hj : j ≤ 8000) :
    endpointDecayQ q j = fixedQ (endpointDecayState q j).decay := by
  rw [endpointDecayState_correct q j hlo hhi hj]
  exact endpointEntropyState_decay endpointLogUpper (endpointDecayBase_eq q hlo hhi) j

end SingularValueBounds.KL.Certificates
