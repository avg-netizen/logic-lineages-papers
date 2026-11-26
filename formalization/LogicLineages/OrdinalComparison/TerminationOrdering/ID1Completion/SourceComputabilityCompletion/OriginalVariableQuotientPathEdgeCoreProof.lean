module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathBottomProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerConstructorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.TypingCoreProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathEdgeCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalVariableQuotientPath
open OriginalVariableRepresentative (selectedData windowGraph)
open InternalParameterizedCanonicalResultFold
open InternalParameterizedCanonicalResultFoldConsumerProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (OTerm z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalQuotientComparisonProof (orRight)
open UniformCertificateCompletion
open UniformCertificateCompletion.SupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Apply the paid first target at the same literal selected tuple. -/
theorem bottomFoldIff (data : Data) (window : Program 1) (out input typ parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Gamma (graph2 (validity (selectedData data window)) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ input)))
    (hn : Nonempty (Derivation body Gamma (foldGraph (selectedData data window) out input parameter))) :
    Nonempty (Derivation body Gamma ((bottomAccepted out).iff (bottomAccepted input))) := by
  have hfull : FullFoldBottomPreservation (selectedData data window) window :=
    OriginalVariableQuotientPathBottomProof.fullFoldBottomPreservation
      (SpineApplicationTargets.parameters (OriginalVariableRepresentative.baseData data window) window) window
  obtain ⟨h⟩ := hfull body α Gamma out input typ parameter
  obtain ⟨hp⟩ := andIntro hw (andIntro (andIntro hv hl) hn)
  exact ⟨Derivation.implicationElimination h hp⟩

/-- Reverse rigidity identifies the raw source of an accepted quotient
edge with its variable endpoint. All required original graphs are supplied
by the actual factorization and internally bound left-field witness. -/
theorem variableSourceEquality (data : Data) (window : Program 1)
    (out input typ parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Gamma (graph2 (validity (selectedData data window)) (suc z) input parameter)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typ input)))
    (hn : Nonempty (Derivation body Gamma (foldGraph (selectedData data window) out input parameter)))
    (hvar : Nonempty (Derivation body Gamma (variableAccepted out))) :
    Nonempty (Derivation body Gamma (eqn out input)) := by
  obtain ⟨hvar⟩ := hvar
  obtain ⟨h⟩ := OriginalVariableRepresentativeRigidityProof.fullFoldRigidity data window
    body α Gamma out input typ parameter
  obtain ⟨hp⟩ := andIntro hw (andIntro (andIntro hv hl) (andIntro hn ⟨orRight hvar⟩))
  simpa only [equalEqn] using
    (Nonempty.intro (Derivation.implicationElimination h hp))

/-- Both actual representative graphs and the normalized old step are
used without changing any raw endpoint, certificate or parameter. -/
theorem variableAtRawType (data : Data) (window : Program 1) (oldStep : Program 4)
    (x y s t k typeCode sourceType parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window x parameter)))
    (hr : Nonempty (Derivation body Gamma
      (requirements (selectedData data window) (OriginalConstructorLeaf.refined oldStep) x y s t k parameter)))
    (hv : Nonempty (Derivation body Gamma (variableAccepted x)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typeCode x)))
    (hs : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left sourceType s))) :
    Nonempty (Derivation body Gamma (graph1 BottomRepresentative.bottomCode y typeCode)) := by
  let selected := selectedData data window
  have hstep := andLeft hr
  obtain ⟨hvs,hvt,_⟩ := TypingProof.stepParts selected (OriginalConstructorLeaf.refined oldStep)
    s t k parameter hstep
  have hn := TypingProof.sourceFold selected x s parameter hvs (andLeft (andRight hr))
  have hws := BottomDescentStepProof.windowChange window (suc z) x s parameter hw
  have he := variableSourceEquality data window x s sourceType parameter hws hvs hs hn hv
  have hvar := headTransport OriginalConstructorLeaf.variableTest (suc z) x s Fin.elim0 he hv
  have hleft := headTransport InternalUnpair.left typeCode x s Fin.elim0 he hl
  obtain ⟨hc⟩ := (OriginalNonapplicationCheckerConstructorProof.normalizedCases selected oldStep
    body α Gamma s t k parameter typeCode).1
  obtain ⟨hp⟩ := andIntro hstep (andIntro hvar hleft)
  have hb : Nonempty (Derivation body Gamma (graph1 BottomRepresentative.bottomCode t typeCode)) :=
    ⟨Derivation.implicationElimination hc hp⟩
  have hlt := BottomSourceShapeProof.bottomCodeLeft t typeCode hb
  have hbt := BottomSourceShapeProof.bottomAccept t typeCode hb
  have hnt := andRight (andRight hr)
  have hwt := BottomDescentStepProof.windowChange window (suc z) x t parameter hw
  obtain ⟨hi⟩ := bottomFoldIff data window y t typeCode parameter hwt hvt hlt hnt
  obtain ⟨hbt⟩ := hbt
  have hby : Nonempty (Derivation body Gamma (bottomAccepted y)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hi) hbt⟩
  have hcert := certifiedAt selected y t typeCode parameter hvt hlt hnt
  exact BottomSourceShapeProof.bottomRecover y typeCode
    (andLeft (andRight (andRight hcert))) hby

/-- Reverse bottom recognition pushes terminality back to the actual raw
source, where the paid normalized constructor case rejects the very step. -/
theorem bottomAtRawType (data : Data) (window : Program 1) (oldStep : Program 4)
    (x y s t k sourceType parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma (windowGraph window x parameter)))
    (hr : Nonempty (Derivation body Gamma
      (requirements (selectedData data window) (OriginalConstructorLeaf.refined oldStep) x y s t k parameter)))
    (hb : Nonempty (Derivation body Gamma (bottomAccepted x)))
    (hs : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left sourceType s))) :
    Nonempty (Derivation body Gamma ⊥) := by
  let selected := selectedData data window
  have hstep := andLeft hr
  obtain ⟨hvs,_,_⟩ := TypingProof.stepParts selected (OriginalConstructorLeaf.refined oldStep)
    s t k parameter hstep
  have hn := TypingProof.sourceFold selected x s parameter hvs (andLeft (andRight hr))
  have hws := BottomDescentStepProof.windowChange window (suc z) x s parameter hw
  obtain ⟨hi⟩ := bottomFoldIff data window x s sourceType parameter hws hvs hs hn
  obtain ⟨hb⟩ := hb
  have hbs := Derivation.implicationElimination (Derivation.conjunctionLeft hi) hb
  obtain ⟨hc⟩ := (OriginalNonapplicationCheckerConstructorProof.normalizedCases selected oldStep
    body α Gamma s t k parameter sourceType).2
  obtain ⟨hstep⟩ := hstep
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination hc hbs) hstep⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPathEdgeCoreProof
