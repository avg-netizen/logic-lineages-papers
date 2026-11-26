module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalSourceCheckProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBranchValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaNodeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalTransparentLambdaValidity OriginalTransparentLambdaValidityInternal
open OriginalHereditaryValidityInternal
open OriginalTransparentLambdaValidityInternalSourceCheckProof OriginalTransparentLambdaValidityInternalShapeAcceptanceProof
open OriginalTransparentLambdaValidityInternalBranchSupportProof OriginalTransparentLambdaValidityInternalBranchValueProof
open OriginalTransparentLambdaValidityInternalLambdaSupportProof
open InternalApplicationStepPeelSupportProof (andLeft)
open InternalAcceptanceConjunctionProof (conjunctionRecover)
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem sourceNodeRecover (data : Data) (raw parameter : OTerm alpha)
    (htag : Nonempty (Derivation body Gamma (TagIs 1 raw)))
    (hn : Nonempty (Derivation body Gamma
      (NodeFactors (sourceRoot data) (targetRoot data) data.member raw parameter))) :
    Nonempty (Derivation body Gamma (SourceLambdaRootFactors data raw parameter)) :=
  sourceCheckRecover data raw parameter
    (dispatchOne data.oldSource (sourceCheck data) (numeral 1) raw parameter htag (andLeft hn))

theorem sourceNodeValue (data : Data) (raw parameter : OTerm alpha)
    (htag : Nonempty (Derivation body Gamma (TagIs 1 raw)))
    (hf : Nonempty (Derivation body Gamma (SourceLambdaRootFactors data raw parameter))) :
    Nonempty (Derivation body Gamma
      (NodeFactors (sourceRoot data) (targetRoot data) data.member raw parameter)) := by
  have hc := sourceCheckValue data raw parameter hf
  have hshape := andLeft (conjunctionRecover _ _ (Fin.cons raw (Fin.cons parameter Fin.elim0)) hc)
  exact nodeAtLambda (sourceRoot data) (targetRoot data) data.member raw parameter
    (dispatchOneValue data.oldSource (sourceCheck data) (numeral 1) raw parameter htag hc)
    (dispatchOneValue data.oldTarget lambdaShape (numeral 1) raw parameter htag hshape) htag

theorem sourceNodeEquation (data : Data) (raw parameter : OTerm alpha)
    (htag : Nonempty (Derivation body Gamma (TagIs 1 raw))) :
    Nonempty (Derivation body Gamma
      ((NodeFactors (sourceRoot data) (targetRoot data) data.member raw parameter).iff
        (SourceLambdaRootFactors data raw parameter))) := by
  let A := NodeFactors (sourceRoot data) (targetRoot data) data.member raw parameter
  let B := SourceLambdaRootFactors data raw parameter
  obtain ⟨hf⟩ := sourceNodeRecover data raw parameter (addAssumption htag A)
    (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := sourceNodeValue data raw parameter (addAssumption htag B)
    (show Nonempty (Derivation body (B :: Gamma) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem targetNodeRecover (data : Data) (raw parameter : OTerm alpha)
    (htag : Nonempty (Derivation body Gamma (TagIs 1 raw)))
    (hn : Nonempty (Derivation body Gamma
      (NodeFactors (targetRoot data) (InternalLessThan.constantOne 2)
        (InternalLessThan.constantOne 2) raw parameter))) :
    Nonempty (Derivation body Gamma (LambdaShape raw)) :=
  shapeRecover raw parameter
    (dispatchOne data.oldTarget lambdaShape (numeral 1) raw parameter htag (andLeft hn))

theorem targetNodeValue (data : Data) (raw parameter : OTerm alpha)
    (htag : Nonempty (Derivation body Gamma (TagIs 1 raw)))
    (hf : Nonempty (Derivation body Gamma (LambdaShape raw))) :
    Nonempty (Derivation body Gamma
      (NodeFactors (targetRoot data) (InternalLessThan.constantOne 2)
        (InternalLessThan.constantOne 2) raw parameter)) :=
  nodeAtLambda (targetRoot data) (InternalLessThan.constantOne 2) (InternalLessThan.constantOne 2)
    raw parameter (dispatchOneValue data.oldTarget lambdaShape (numeral 1) raw parameter htag
      (shapeValue raw parameter hf))
    (InternalLessThanSupportProof.oneConstantValue (Fin.cons raw (Fin.cons parameter Fin.elim0))) htag

theorem targetNodeEquation (data : Data) (raw parameter : OTerm alpha)
    (htag : Nonempty (Derivation body Gamma (TagIs 1 raw))) :
    Nonempty (Derivation body Gamma
      ((NodeFactors (targetRoot data) (InternalLessThan.constantOne 2)
        (InternalLessThan.constantOne 2) raw parameter).iff (LambdaShape raw))) := by
  let A := NodeFactors (targetRoot data) (InternalLessThan.constantOne 2)
    (InternalLessThan.constantOne 2) raw parameter
  let B := LambdaShape raw
  obtain ⟨hf⟩ := targetNodeRecover data raw parameter (addAssumption htag A)
    (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := targetNodeValue data raw parameter (addAssumption htag B)
    (show Nonempty (Derivation body (B :: Gamma) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaNodeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaNodeProof
