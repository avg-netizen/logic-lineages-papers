module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransportSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalLambdaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankObjectProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalRawObjectTransport OriginalRawObjectTransportInternalSyntaxProof
open OriginalCanonicalizedObjectTypedTransportSupportProof
open UniformCertificateCompletion OriginalFinalGuardedRank
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The literal Object observer is the raw observer of its actual right coordinate. -/
theorem objectRankAtPair (rank object gamma raw : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing object gamma raw))) :
    Nonempty (Derivation body Delta
      ((graph1 variableRankObjectRaw rank object).iff
        (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank raw))) :=
  OriginalFinalVariableWeakeningSupportProof.compositionEquation
    OriginalRawSyntaxTransport.variableRankPackedRaw (fun _ : Fin 1 => InternalUnpair.right)
    rank (Fin.cons object Fin.elim0) (Fin.cons raw Fin.elim0)
    (fun i => Fin.cases (pairRight object gamma raw hp) (fun j => Fin.elim0 j) i)

/-- Recover all coordinates and source premises from the genuine Object
wrapper and active outer typed graph, then apply the exact final fold invariant. -/
theorem objectRank (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (law : FinalRankLaw p H G W) : ObjectRankLaw p H G W := by
  intro positive alpha Delta context out input typ rank
  let r := refined p H G W
  let f := OriginalLambdaTraversalSelection.finalInputs r
  let D := OriginalLambdaTraversalSelection.finalData r
  let K := OriginalFinalVariableObject.canonicalObjectProgram r
  let A := graph1 f.window (numeral 1) (numeral context) ⊓
    (graph3 (GlobalSourcePackage.computability f).typed (numeral 1) (numeral context) typ input ⊓
      graph2 K out (numeral context) input)
  have ha : Nonempty (Derivation positive (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hw := andLeft ha
  have ht := andLeft (andRight ha)
  have hk := andRight (andRight ha)
  suffices h : Nonempty (Derivation positive (A :: Delta)
      ((graph1 variableRankObjectRaw rank out).iff (graph1 variableRankObjectRaw rank input))) by
    obtain ⟨h⟩ := h
    exact ⟨Derivation.implicationIntroduction h⟩
  apply (OriginalFinalVariableObjectExposureProof.actualOriginalFinalVariableObjectExposure r).1
    positive alpha (A :: Delta) (numeral context) input out _ hk
  intro beta j Theta hj gamma raw parameter canonicalRaw hex
  change Nonempty (Derivation positive Theta
    (((graph1 variableRankObjectRaw rank out).relabel j).iff
      ((graph1 variableRankObjectRaw rank input).relabel j)))
  rw [graph1Rename, graph1Rename]
  have hw' := windowRename f.window context hw j Theta hj
  have ht' := outerTypedRename (GlobalSourcePackage.computability f).typed context typ input ht j Theta hj
  have hinput := andLeft hex
  have hparameter := andLeft (andRight hex)
  have hfold := andLeft (andRight (andRight hex))
  have hout := andRight (andRight (andRight hex))
  simp only [numeralRename] at hparameter
  have htyped := OuterCarrierSupportProof.typedRecover f.oldComp D f.window
    f.oldVertex f.oldResult context (typ.relabel j) (input.relabel j) gamma raw parameter
    hw' (pairLeft _ _ _ hinput) (pairRight _ _ _ hinput) hparameter ht'
  have hfactors := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    D.oldRepresentative (InternalOriginalUniformDescentSelection.validity D) D.member
    raw (typ.relabel j) parameter htyped
  have hsource := andIntro (andLeft (andRight hfactors)) (andLeft (andRight (andRight hfactors)))
  let xs : Fin 2 → OTerm beta := Fin.cons raw (Fin.cons parameter Fin.elim0)
  have hcontext := unaryValue InternalUnpair.left (.projection 1) (numeral context) parameter xs
    (pairLeft _ _ _ hparameter) (projectionValue 1 xs)
  have hwindow := unaryValue f.window (leftOf (.projection 1)) (numeral 1) (numeral context) xs hw' hcontext
  obtain ⟨hl⟩ := law positive beta Theta canonicalRaw raw (typ.relabel j) parameter (rank.relabel j)
  obtain ⟨hargs⟩ := andIntro hwindow (andIntro hsource hfold)
  have hraw := show Nonempty (Derivation positive Theta _) from
    ⟨Derivation.implicationElimination hl hargs⟩
  have hi := objectRankAtPair (rank.relabel j) (input.relabel j) gamma raw hinput
  have ho := objectRankAtPair (rank.relabel j) (out.relabel j) gamma canonicalRaw hout
  obtain ⟨hi⟩ := hi
  have hiReverse := show Nonempty (Derivation positive Theta
      ((graph1 OriginalRawSyntaxTransport.variableRankPackedRaw (rank.relabel j) raw).iff
        (graph1 variableRankObjectRaw (rank.relabel j) (input.relabel j)))) from
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionRight hi) (Derivation.conjunctionLeft hi)⟩
  exact OriginalLambdaTraversalFinalLambdaProof.composeIff _ _ _
    (OriginalLambdaTraversalFinalLambdaProof.composeIff _ _ _ ho hraw) hiReverse

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankObjectProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankObjectProof
