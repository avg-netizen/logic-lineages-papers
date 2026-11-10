module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationInverseValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.TypingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data validity)
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open InternalApplicationCertificateConstructorsSupportProof (unaryRecover)
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalParameterizedCanonicalResultFoldConsumerProof
open InternalTagArithmeticSyntaxProof (suc z)
open UniformCertificateCompletion OriginalApplicationComponentCoherenceFieldsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The requested function's original typed checker and the raw argument's
certified fold restore the whole child types discarded by raw application. -/
theorem requestedFields (data : Data) (window : Program 1)
    (arrow d e function argument x argumentOut parameter : OTerm alpha)
    (hi : Nonempty (Derivation body Gamma
      (OriginalNeutralApplication.InputPremises data window arrow d e function argument parameter)))
    (hr : Nonempty (Derivation body Gamma
      (OriginalNeutralApplication.Recovered data d e function argument x argumentOut parameter))) :
    Nonempty (Derivation body Gamma
      (graph1 (appDomain (.projection 0)) d x ⊓
        (graph1 (outerType (.projection 0)) e x ⊓
          (graph1 functionSelector function x ⊓ graph1 argumentSelector argumentOut x)))) := by
  have htype := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    data.oldRepresentative (validity data) data.member function arrow parameter
    (andLeft (andRight (andRight (andRight hi))))
  have hfType := andLeft (andRight (andRight htype))
  have harg := andRight (andRight (andRight (andRight hi)))
  have hc := certifiedAt data argumentOut argument d parameter
    (andLeft harg) (andRight harg) (andLeft hr)
  exact rawTypedFields arrow d e function argumentOut x
    (andLeft (andRight hi)) hfType (andLeft (andRight (andRight hc))) (andRight hr)

/-- Recover the canonical child types from the literal raw application and
accepted raw step retained by neutral quotient inversion. This pays the
argument-validity obligation before using whole-child selector functionality. -/
theorem quotientFields (data : Data) (oldStep : Program 4)
    (x y certificate parameter S T K state d e arrow f g a k child F G A : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma
      (OriginalNeutralQuotient.Recovered data oldStep x y certificate parameter
        S T K state d e arrow f g a k child F G A))) :
    Nonempty (Derivation body Gamma
      (graph1 (appDomain (.projection 0)) d x ⊓
        (graph1 (outerType (.projection 0)) e x ⊓
          (graph1 functionSelector F x ⊓ graph1 argumentSelector A x)))) := by
  have hrequirements := andLeft (andRight hr)
  have hpeeled := andLeft (andRight (andRight (andRight hr)))
  have hchild := andLeft (andRight (andRight (andRight (andRight hr))))
  have hargument := andRight (andRight (andRight (andRight (andRight hr))))
  have hconstructors := andLeft (andLeft (andRight hpeeled))
  have har := andLeft hconstructors
  have hfType := andLeft (andRight hconstructors)
  have haType := andLeft (andRight (andRight (andRight hconstructors)))
  have htail := andRight (andRight (andRight (andRight hconstructors)))
  have hsapp := andLeft (andRight htail)
  obtain ⟨hvs,_,_⟩ := TypingProof.stepParts data oldStep S T K parameter (andLeft hrequirements)
  have hchildren := OriginalApplicationInverseValidityProof.rawSourceRecover
    data arrow d e f a S parameter har hfType haType hsapp hvs
  have hnf := andLeft (andRight (andRight (andRight hchild)))
  have hfc := certifiedAt data F f arrow parameter (andLeft (andRight hchild)) hfType hnf
  have hac := certifiedAt data A a d parameter
    (andRight (andRight hchildren)) haType (andLeft hargument)
  exact rawTypedFields arrow d e F A x har
    (andLeft (andRight (andRight hfc))) (andLeft (andRight (andRight hac)))
    (andLeft (andRight hargument))

/-- Whole original selectors identify the recovered domain, codomain,
function and argument at the shared canonical source. -/
theorem componentEqualities (data : Data) (window : Program 1) (oldStep : Program 4)
    (arrow d e function argument x y certificate parameter
      S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child F G A argumentOut : OTerm alpha)
    (hi : Nonempty (Derivation body Gamma
      (OriginalNeutralApplication.InputPremises data window arrow d e function argument parameter)))
    (hq : Nonempty (Derivation body Gamma
      (OriginalNeutralApplication.Recovered data d e function argument x argumentOut parameter)))
    (hr : Nonempty (Derivation body Gamma
      (OriginalNeutralQuotient.Recovered data oldStep x y certificate parameter
        S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child F G A))) :
    Nonempty (Derivation body Gamma
      (equal rawD d ⊓ (equal rawE e ⊓ (equal F function ⊓ equal A argumentOut)))) := by
  have hs := quotientFields data oldStep x y certificate parameter
    S T K state rawD rawE rawArrow rawFunction rawTarget rawArgument rawStep child F G A hr
  have ht := requestedFields data window arrow d e function argument x argumentOut parameter hi hq
  let xs : Fin 1 → OTerm alpha := Fin.cons x Fin.elim0
  have hd := valueUnique (appDomain (.projection 0)) rawD d xs (andLeft hs) (andLeft ht)
  have he := valueUnique (outerType (.projection 0)) rawE e xs
    (andLeft (andRight hs)) (andLeft (andRight ht))
  have hf := valueUnique functionSelector F function xs
    (andLeft (andRight (andRight hs))) (andLeft (andRight (andRight ht)))
  have ha := valueUnique argumentSelector A argumentOut xs
    (andRight (andRight (andRight hs))) (andRight (andRight (andRight ht)))
  simpa only [equalEqn] using andIntro hd (andIntro he (andIntro hf ha))

/-- The requested codomain is the literal outer type of its actualJ output. -/
theorem outputType (data : Data) (window : Program 1)
    (arrow d e function argument x argumentOut parameter : OTerm alpha)
    (hi : Nonempty (Derivation body Gamma
      (OriginalNeutralApplication.InputPremises data window arrow d e function argument parameter)))
    (hr : Nonempty (Derivation body Gamma
      (OriginalNeutralApplication.Recovered data d e function argument x argumentOut parameter))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left e x)) := by
  have ht := andLeft (andRight (requestedFields data window
    arrow d e function argument x argumentOut parameter hi hr))
  exact unaryRecover InternalUnpair.left (.projection 0) e x (Fin.cons x Fin.elim0)
    ht (projectionValue 0 (Fin.cons x Fin.elim0))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeFieldsProof
