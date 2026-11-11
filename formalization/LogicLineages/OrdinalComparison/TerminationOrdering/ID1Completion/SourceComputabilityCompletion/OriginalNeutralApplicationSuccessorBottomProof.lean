module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorBottomPathProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorBottomProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalComputabilityApplication InternalComputabilityApplicationProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedLeastCodeRepresentative (typeNumber)
open OriginalSourceNeutralApplicationFieldsProof
open OriginalNeutralApplicationSuccessorSupportProof
open UniformCertificateCompletion

/-- The ordinary suffix after a literal bottom is an identity by the
original selected leaf's terminality. Typed bottom C uses its internal mark,
not an external assumption that the requested type belongs to the window. -/
theorem bottomCase (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun t => t ∈ S))
    (alpha : Type) (Gamma : List (Formula alpha)) (sigma tau : Ty)
    (F A X Y witness gammaCode function argument x y parameter raw tail vertex cert : OTerm alpha)
    (h : Nonempty (Derivation (SourcePresentation.sourceBody (src p)
      (OrdinaryArithmeticQuotient.contextCode symbols S table)) Gamma
      (OriginalSourceNeutralApplicationPath.RecoveredPrefix (data p) (final p).window (final p).oldStep
        (src p) (comp p) (OrdinaryArithmeticQuotient.contextCode symbols S table) sigma tau
        F A X Y witness gammaCode function argument x y parameter raw tail vertex cert)))
    (hb : Nonempty (Derivation (SourcePresentation.sourceBody (src p)
      (OrdinaryArithmeticQuotient.contextCode symbols S table)) Gamma
      (graph1 BottomRepresentative.bottomCode vertex (numeral (typeNumber tau))))) :
    Nonempty (Derivation (SourcePresentation.sourceBody (src p)
      (OrdinaryArithmeticQuotient.contextCode symbols S table)) Gamma
      (computable (comp p) tau (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)) Y)) := by
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := final p
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  have hi := andLeft (andLeft h)
  have hwp := andLeft (inputPremisesOf hi)
  have hwv := BottomDescentStepProof.windowChange r.window InternalOriginalStepGuard.one
    function vertex parameter hwp
  have ht := andRight (andRight (andRight (andRight h)))
  have he := OriginalNeutralApplicationSuccessorBottomPathProof.finalBottomPathIdentity p
    vertex y tail parameter hwv
    (BottomSourceShapeProof.bottomAccept vertex (numeral (typeNumber tau)) hb) ht
  obtain ⟨he⟩ := he
  rw [equalEqn] at he
  have hyb := outputTransport BottomRepresentative.bottomCode vertex y
    (Fin.cons (numeral (typeNumber tau)) Fin.elim0) ⟨InternalTagArithmeticSupportProof.symm he⟩ hb
  have hyp := andLeft (andRight (andRight (andRight (andRight (andLeft h)))))
  have hbottom := OriginalVariableObjectSupportProof.bottomObjectAccept Y gammaCode y
    (numeral (typeNumber tau)) (pairLeft Y gammaCode y hyp) (pairRight Y gammaCode y hyp) hyb
  have hmark := GlobalSourceSpineBottomSupportProof.bottomObjectMarked tau Y gammaCode hbottom
  have hyt := prefixTargetTyped n arity p hp symbols S table hS sigma tau
    F A X Y witness gammaCode function argument x y parameter raw tail vertex cert h
  have hq := OriginalSpineGuardLeafProof.refinedInputsCalibrated n arity p hp
  have hr := OriginalApplicationComponentCoherenceGlobalInputProof.finalInputsCalibrated n arity q hq
  exact GlobalSourceSpineComputableProof.computableSpine n arity r.base hr.1 r.window hr.2.1
    r.oldSrc r.oldComp r.oldStep r.oldVertex r.oldResult symbols S table hS
    tau alpha Gamma Y (numeral (Nat.pair 1 0)) (numeral 0) hyt hmark

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorBottomProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorBottomProof
