module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationStepPeelSupportProof
open InternalApplicationCertificateConstructors InternalRepresentativeApplicationCongruence
open InternalRepresentativeApplicationCongruenceApplicationProof InternalTagArithmeticSupportProof

theorem actualOriginalRepresentativePayloadTransport :
    InternalRepresentativeApplicationCongruenceTargets.ActualOriginalRepresentativePayloadTransport :=
  InternalRepresentativeApplicationCongruencePayloadProof.actualOriginalRepresentativePayloadTransport

theorem actualOriginalCertifiedSourceRepresentativeApplicationCongruence :
    InternalRepresentativeApplicationCongruenceTargets.ActualOriginalCertifiedSourceRepresentativeApplicationCongruence := by
  intro body validity member old α arrow d e fp ap fn arg parent x out
  let premise := graph1 (data validity member old).sourceRepresentative x fn ⊓
    applicationPremises validity member old arrow d e fp ap fn arg parent x out
  have h : Nonempty (Derivation body [premise] premise) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨result⟩ := sourceApplication validity member old arrow d e fp ap fn arg parent x out
    (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction result⟩

theorem actualOriginalCertifiedTargetRepresentativeApplicationCongruence :
    InternalRepresentativeApplicationCongruenceTargets.ActualOriginalCertifiedTargetRepresentativeApplicationCongruence := by
  intro body validity member old α arrow d e fp ap fn arg parent x out
  let premise := graph1 (data validity member old).targetRepresentative x fn ⊓
    applicationPremises validity member old arrow d e fp ap fn arg parent x out
  have h : Nonempty (Derivation body [premise] premise) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨result⟩ := targetApplication validity member old arrow d e fp ap fn arg parent x out
    (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction result⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruenceProof
