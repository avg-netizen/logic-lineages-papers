module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafEquationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar OriginalApplicationComponentCoherenceFieldsProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeel (appDomain outerType)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The exact source packet from the frozen paired contract. No success,
fixedness or canonical child type is inserted into this antecedent. -/
def source (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg parent functionOut argumentOut out parameter : OTerm alpha) : Formula alpha :=
  OriginalFunctionNeutrality.windowGraph window parent parameter ⊓
    (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent ⊓
      (graph2 (InternalOriginalUniformDescentSelection.validity (selectedData data window))
        InternalOriginalStepGuard.one parent parameter ⊓
        (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) functionOut fn parameter ⊓
          (InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) argumentOut arg parameter ⊓
            InternalParameterizedCanonicalResultFold.foldGraph (selectedData data window) out parent parameter))))

/-- The SAME final-leaf application equation supplies the raw constructor.
Original child validity and the actual canonical consumer restore the types
that the raw application program itself discards. -/
theorem canonicalFields (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg parent functionOut argumentOut out parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Delta
      (source data window arrow d e fp ap fn arg parent functionOut argumentOut out parameter))) :
    Nonempty (Derivation body Delta
      (graph1 (appDomain (.projection 0)) d out ⊓
        (graph1 (outerType (.projection 0)) e out ⊓
          (graph1 functionSelector functionOut out ⊓ graph1 argumentSelector argumentOut out)))) := by
  have hw := andLeft hs
  have hc := andLeft (andRight hs)
  have hv := andLeft (andRight (andRight hs))
  have hf := andLeft (andRight (andRight (andRight hs)))
  have ha := andLeft (andRight (andRight (andRight (andRight hs))))
  have hn := andRight (andRight (andRight (andRight (andRight hs))))
  have hr := OriginalApplicationSidecarSameLeafEquationProof.canonicalRecover data window
    arrow d e fp ap fn arg parent functionOut argumentOut out parameter hw hc hv hf ha hn
  have children := OriginalApplicationInverseValidityProof.sourceRecover (selectedData data window)
    arrow d e fp ap fn arg parent parameter hc hv
  have hfl := pairLeft fn arrow fp (andLeft (andRight hc))
  have hal := pairLeft arg d ap (andLeft (andRight (andRight hc)))
  have hfi := andRight (InternalParameterizedCanonicalResultFoldConsumerProof.certifiedAt
    (selectedData data window) functionOut fn arrow parameter (andLeft (andRight children)) hfl hf)
  have hai := andRight (InternalParameterizedCanonicalResultFoldConsumerProof.certifiedAt
    (selectedData data window) argumentOut arg d parameter (andRight (andRight children)) hal ha)
  exact rawTypedFields arrow d e functionOut argumentOut out
    (andLeft hc) (andLeft (andRight hfi)) (andLeft (andRight hai)) hr

/-- Original raw projection functionality compares both reconstructed whole
children, not just their stored payloads. -/
theorem actualOriginalApplicationComponentCoherence :
    OriginalApplicationComponentCoherenceTargets.ActualOriginalApplicationComponentCoherence := by
  intro body data window alpha Delta arrow d e fp ap fn arg parent functionOut argumentOut
    arrow' d' e' fp' ap' fn' arg' parent' functionOut' argumentOut' out parameter
  let P := source data window arrow d e fp ap fn arg parent functionOut argumentOut out parameter ⊓
    source data window arrow' d' e' fp' ap' fn' arg' parent' functionOut' argumentOut' out parameter
  have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hs := canonicalFields data window arrow d e fp ap fn arg parent functionOut argumentOut out parameter
    (andLeft hp)
  have ht := canonicalFields data window arrow' d' e' fp' ap' fn' arg' parent' functionOut' argumentOut' out parameter
    (andRight hp)
  let xs : Fin 1 → OTerm alpha := Fin.cons out Fin.elim0
  have hd := valueUnique (appDomain (.projection 0)) d d' xs (andLeft hs) (andLeft ht)
  have he := valueUnique (outerType (.projection 0)) e e' xs
    (andLeft (andRight hs)) (andLeft (andRight ht))
  have hf := valueUnique functionSelector functionOut functionOut' xs
    (andLeft (andRight (andRight hs))) (andLeft (andRight (andRight ht)))
  have ha := valueUnique argumentSelector argumentOut argumentOut' xs
    (andRight (andRight (andRight hs))) (andRight (andRight (andRight ht)))
  have hc : Nonempty (Derivation body (P :: Delta)
      (equal d d' ⊓ (equal e e' ⊓ (equal functionOut functionOut' ⊓ equal argumentOut argumentOut')))) := by
    simpa only [equalEqn] using andIntro hd (andIntro he (andIntro hf ha))
  obtain ⟨h⟩ := hc
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceProof.actualOriginalApplicationComponentCoherence
