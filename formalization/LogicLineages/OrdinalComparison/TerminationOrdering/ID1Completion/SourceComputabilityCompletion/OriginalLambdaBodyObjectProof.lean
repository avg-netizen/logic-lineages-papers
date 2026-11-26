module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObjectSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObjectProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalTagArithmeticSupportProof (refl)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalLambdaBodyObject OriginalLambdaBodyObjectSupportProof
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All coordinates are internally bound actual query outputs. Original
outer typing pays the parent's final fixedness, while the unchanged original
universe checker pays the body's member at its literal extended parameter. -/
theorem actualOriginalLambdaBodyObjectExposure :
    OriginalLambdaBodyObjectTargets.ActualOriginalLambdaBodyObjectExposure := by
  intro p H G W positive alpha Delta context typ input psi hinput step
  apply programsCases (runtimeQueries context) (Fin.cons input Fin.elim0) psi
  intro beta j Theta ys hj hs
  simp only [consTermRename,emptyRename] at hs
  have hinput' : Nonempty (Derivation positive Theta
      (Premise p H G W context (typ.relabel j) (input.relabel j))) := by
    simpa only [Premise,conjunctionRename,graph1Rename,graph3Rename,numeralRename]
      using renameInto hinput j Theta hj
  have hfields := fieldsFromQueries context (input.relabel j) ys
    (andRight (andRight hinput')) hs
  exact step beta j Theta hj (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)
    (ys 5) (ys 6) (ys 7) (ys 8)
    (recoveredAtFields p H G W context (typ.relabel j) (input.relabel j)
      (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8)
      hinput' (andLeft hfields) (andLeft (andRight hfields))
      (andLeft (andRight (andRight hfields))) (andRight (andRight (andRight hfields))))

/-- Functionality identifies any supplied extractor outputs with the actual
internally exposed codomain and body. The original outer typed graph receives
those equal inputs; no transformed typedness or body fixedness is assumed. -/
theorem actualOriginalLambdaBodyObjectTyped :
    OriginalLambdaBodyObjectTargets.ActualOriginalLambdaBodyObjectTyped := by
  intro p H G W positive alpha Delta context typ input e childObject
  let Q := Premise p H G W context typ input ⊓
    (graph1 codomainCode e input ⊓ graph1 bodyObject childObject input)
  have hq : Nonempty (Derivation positive (Q :: Delta) Q) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hout : Nonempty (Derivation positive (Q :: Delta)
      (graph3 (GlobalSourcePackage.computability (finalInputs p H G W)).typed
        (numeral 1) (numeral context) e childObject)) := by
    apply actualOriginalLambdaBodyObjectExposure p H G W positive alpha (Q :: Delta)
      context typ input _ (andLeft hq)
    intro beta j Theta hj gamma raw d actualE bodyRaw parameter extended bodyParameter actualBody h
    simp only [graph3Rename,numeralRename]
    have hq' := renameInto (andRight hq) j Theta hj
    simp only [conjunctionRename,graph1Rename] at hq'
    have hex := andRight (andRight (andRight (andRight h)))
    have he := valueUnique codomainCode actualE (e.relabel j)
      (Fin.cons (input.relabel j) Fin.elim0) (andLeft hex) (andLeft hq')
    have hb := valueUnique bodyObject actualBody (childObject.relabel j)
      (Fin.cons (input.relabel j) Fin.elim0) (andLeft (andRight hex)) (andRight hq')
    have ht := andRight (andRight (andRight (andRight hex)))
    apply InternalGraphCompositionEqualityProof.graphInputTransport positive beta 3 Theta _
      (numeral 1)
      (Fin.cons (numeral context) (Fin.cons actualE (Fin.cons actualBody Fin.elim0)))
      (Fin.cons (numeral context)
        (Fin.cons (e.relabel j) (Fin.cons (childObject.relabel j) Fin.elim0))) _ ht
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
    · rw [InternalSourceInversionSupportProof.onEquality]
      exact ⟨refl (numeral context)⟩
    · rw [InternalSourceInversionSupportProof.onEquality]
      exact he
    · rw [InternalSourceInversionSupportProof.onEquality]
      exact hb
  obtain ⟨hout⟩ := hout
  exact ⟨Derivation.implicationIntroduction hout⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObjectProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObjectProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObjectProof.actualOriginalLambdaBodyObjectExposure
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObjectProof.actualOriginalLambdaBodyObjectTyped
