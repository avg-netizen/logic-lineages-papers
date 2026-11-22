module
public import LogicLineages.PermittedControl.ActualCanonicalNormalizedTapeTargets
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingReadProof
import LogicLineages.PermittedControl.ActualNormalizedTapeCertificateProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalNormalizedTape
open ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualNormalizedTape ActualCanonicalOperandGrouping ActualZeroClassOutsideAndShift

theorem exactCanonicalTapeCertificate : ExactCanonicalTapeCertificate := by
  intro f ρ raw xs allReads canonicalCode
  obtain ⟨old,oldCode,_,_,_,_,_⟩ := (exactNormalizedReads f ρ raw).2 allReads
  have original := exactLegacyTape f ρ raw old allReads oldCode
  obtain ⟨out,outCode,perm,_,trueReads,value⟩ := (exactCanonicalReads f ρ raw).2 old oldCode
  have same : out = xs := Option.some.inj (outCode.symm.trans canonicalCode)
  subst out
  have permKeys : (originalKeys xs).Perm (originalKeys old) := perm.map (fun rd => rd.1.2)
  refine ⟨allReads,trueReads,permKeys.nodup_iff.mpr original.unique,?_,value.symm,?_⟩
  · intro key
    exact permKeys.mem_iff.trans (original.covers key)
  · intro rd used
    exact original.records rd (perm.mem_iff.mp used)

theorem exactCanonicalTapeDomain : ExactCanonicalTapeDomain := by
  intro f ρ raw
  constructor
  · intro allReads
    obtain ⟨old,oldCode,_,_,_,_,_⟩ := (exactNormalizedReads f ρ raw).2 allReads
    obtain ⟨out,code,_,_,_,_⟩ := (exactCanonicalReads f ρ raw).2 old oldCode
    exact ⟨out,code,exactCanonicalTapeCertificate f ρ raw out allReads code⟩
  · rintro ⟨_,_,certificate⟩
    exact certificate.sourceReads

end LogicLineages.PermittedControl.ActualCanonicalNormalizedTape
