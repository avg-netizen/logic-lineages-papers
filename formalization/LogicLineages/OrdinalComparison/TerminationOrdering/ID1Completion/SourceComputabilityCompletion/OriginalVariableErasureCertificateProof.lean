module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateRawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion OriginalRawObjectTransport
open OriginalVariableErasureCertificate OriginalVariableErasureCertificateTargets
open OriginalVariableErasureCertificateSourceProof (targetBottom)
open OriginalVariableErasureCertificateRawProof (rawResult)
open OriginalFinalVariableObjectInternalSupportProof (secondTransport)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The original certificate first determines its successor. Actual raw
erasure of both original endpoints then gives the collapse and strict rank
branch; no transformed certificate or endpoint fact is assumed. -/
theorem collapse (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (context : Nat) (tau : Ty)
    (source target witness gamma extended packed raw erasedSource erasedTarget : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (Premise p H G W context tau source target witness gamma extended packed raw)))
    (hes : Nonempty (Derivation body Delta (graph1 eraseObjectRaw erasedSource source)))
    (het : Nonempty (Derivation body Delta (graph1 eraseObjectRaw erasedTarget target))) :
    Nonempty (Derivation body Delta
      (RawResult tau source target gamma extended erasedSource erasedTarget)) :=
  rawResult tau source target gamma extended packed raw erasedSource erasedTarget
    (andLeft (andRight (andRight h)))
    (targetBottom p H G W context tau source target witness gamma extended packed raw h) hes het

theorem actualOriginalVariableErasureCertificateCollapse :
    ActualOriginalVariableErasureCertificateCollapse := by
  intro p H G W body alpha Delta context tau
    source target witness gamma extended packed raw erasedSource erasedTarget
  let A := Premise p H G W context tau source target witness gamma extended packed raw ⊓
    (graph1 eraseObjectRaw erasedSource source ⊓ graph1 eraseObjectRaw erasedTarget target)
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := collapse p H G W context tau source target witness gamma extended packed raw
    erasedSource erasedTarget (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction hr⟩

/-- Program functionality at equal raw erased inputs gives equal outputs
of the identical final K. No canonical fixedness or raw erased typing is
needed for this collapse case. The original endpoint rank decrease remains
the one established before either erasure or canonicalization. -/
theorem actualOriginalVariableErasureCertificateCanonicalCollapse :
    ActualOriginalVariableErasureCertificateCanonicalCollapse := by
  intro p H G W
  dsimp only [CanonicalCollapseLaw]
  intro body alpha Delta context tau source target witness gamma extended packed raw
    erasedSource erasedTarget canonicalSource canonicalTarget
  let r := OriginalFinalGuardedRank.refined p H G W
  let K := OriginalFinalVariableObject.canonicalObjectProgram r
  let A := Premise p H G W context tau source target witness gamma extended packed raw ⊓
    (graph1 eraseObjectRaw erasedSource source ⊓
      (graph1 eraseObjectRaw erasedTarget target ⊓
        (graph2 K canonicalSource (numeral context) erasedSource ⊓
          graph2 K canonicalTarget (numeral context) erasedTarget)))
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hr := collapse p H G W context tau source target witness gamma extended packed raw
    erasedSource erasedTarget (andLeft h) (andLeft (andRight h))
    (andLeft (andRight (andRight h)))
  have he := andLeft (andRight (andRight (andRight hr)))
  have hsource := andLeft (andRight (andRight (andRight h)))
  have htarget := andRight (andRight (andRight (andRight h)))
  have hsourceAtTarget := secondTransport K canonicalSource (numeral context)
    erasedSource erasedTarget he hsource
  have heq := valueUnique K canonicalSource canonicalTarget
    (Fin.cons (numeral context) (Fin.cons erasedTarget Fin.elim0)) hsourceAtTarget htarget
  have hout : Nonempty (Derivation body (A :: Delta) (equal canonicalSource canonicalTarget)) := by
    simpa only [equalEqn] using heq
  obtain ⟨hresult⟩ := andIntro hr hout
  exact ⟨Derivation.implicationIntroduction hresult⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateProof
