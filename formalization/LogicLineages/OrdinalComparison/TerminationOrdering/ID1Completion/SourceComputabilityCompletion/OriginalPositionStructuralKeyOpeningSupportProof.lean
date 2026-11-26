module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalGraphComposition InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalAcceptanceConjunctionProof
open UniformCertificateCompletion OriginalPositionStructuralKeyOpeningDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Window depends on the unchanged outer context, not the deleted Gamma. -/
theorem windowAtPair (window : Program 1) (value parameter erased erasedParam context gamma deleted : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (he : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedParam context deleted)))
 (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window value parameter))) :
 Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window erased erasedParam)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons value (Fin.cons parameter Fin.elim0)
 let ys : Fin 2 → OTerm alpha := Fin.cons erased (Fin.cons erasedParam Fin.elim0)
 have hx := unaryValue InternalUnpair.left (.projection 1) context parameter xs
   (pairLeft parameter context gamma hp) (projectionValue 1 xs)
 have hwindow := unaryRecover window (leftOf (.projection 1)) InternalOriginalStepGuard.one context xs hw hx
 have hy := unaryValue InternalUnpair.left (.projection 1) context erasedParam ys
   (pairLeft erasedParam context deleted he) (projectionValue 1 ys)
 exact unaryValue window (leftOf (.projection 1)) InternalOriginalStepGuard.one context ys hwindow hy

theorem activeAtOriginalSource (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (value parameter : OTerm alpha)
 (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph p.window value parameter)))
 (hs : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) value parameter))) :
 Nonempty (Derivation body Delta (OriginalStructuralClassKeyDefinitions.Active p H G W value parameter)) := by
 have hold := OriginalStructuralKeyActivationProof.oldLeafSource p H G W value parameter hs
 change Nonempty (Derivation body Delta
   (graph2 (OriginalFunctionNeutrality.active
     (OriginalLambdaTraversalSelection.transparentData (OriginalStructuralClassKeyDefinitions.prior p H G W).base)
     p.window) InternalOriginalStepGuard.one value parameter))
 rw [OriginalLambdaTraversalFinalGuardProof.activeLeaf]
 exact conjunctionAccept _ _ (Fin.cons value (Fin.cons parameter Fin.elim0)) hw hold

theorem erasedActiveAtCoordinates (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (value parameter erased erasedParam erasedType cutoff context gamma deleted : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (hep : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedParam context deleted)))
 (hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff deleted gamma)))
 (he : Nonempty (Derivation body Delta
   (graph3 OriginalRawSyntaxTransport.erasePackedRaw erased erasedType cutoff value)))
 (hs : Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) value parameter)))
 (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph p.window value parameter))) :
 Nonempty (Derivation body Delta (graph2 (source p H G W) (numeral 1) erased erasedParam)) ∧
 Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph p.window erased erasedParam)) ∧
 Nonempty (Derivation body Delta (OriginalStructuralClassKeyDefinitions.Active p H G W erased erasedParam)) := by
 have hsource := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure
   body alpha Delta H G (InternalOriginalUniformContextMembership.contextMember p.base.member) W
   value erased erasedType cutoff deleted gamma context parameter erasedParam hi he hp hep hs
 have hwindow := windowAtPair p.window value parameter erased erasedParam context gamma deleted hp hep hw
 exact ⟨hsource,hwindow,activeAtOriginalSource p H G W erased erasedParam hwindow hsource⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningSupportProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningSupportProof
