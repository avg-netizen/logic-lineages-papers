module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraIntroductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalAdditionLawsProof (add)
open OriginalRawSyntaxTransportInternalConstructorSubstitutionProof (arityValueAt)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (branchNumeralIntro)
open OriginalStructuralNodeSizeInternalAlgebraProof (rebuild)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem unary (raw first second : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (suc z) raw))) :
    Nonempty (Derivation body Delta (graph3 OriginalStructuralNodeSizeInternalAlgebraProof.rebuild (suc first) raw first second)) := by
  let xs : Fin 3 → OTerm alpha := ![raw,first,second]
  apply branchNumeralIntro 1 1 (arityOf (.projection 0)) _ _ (suc first) xs
    (arityValueAt (.projection 0) (suc z) raw xs (projectionValue 0 xs) ha)
  exact unaryValue .succ (.projection 1) (suc first) first xs
    (successorValue ![first]) (projectionValue 1 xs)

theorem binary (raw first second : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (suc (suc z)) raw))) :
    Nonempty (Derivation body Delta (graph3 OriginalStructuralNodeSizeInternalAlgebraProof.rebuild (suc (add first second)) raw first second)) := by
  let xs : Fin 3 → OTerm alpha := ![raw,first,second]
  apply branchNumeralIntro 2 1 (arityOf (.projection 0)) _ _ (suc (add first second)) xs
    (arityValueAt (.projection 0) (suc (suc z)) raw xs (projectionValue 0 xs) ha)
  exact unaryValue .succ (addOf (.projection 1) (.projection 2)) (suc (add first second)) (add first second) xs
    (successorValue ![add first second])
    (binaryValue InternalArithmeticPrograms.addition (.projection 1) (.projection 2) (add first second)
      first second xs (InternalArithmeticProgramsSupportProof.additionValue first second)
      (projectionValue 1 xs) (projectionValue 2 xs))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraIntroductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraIntroductionProof
