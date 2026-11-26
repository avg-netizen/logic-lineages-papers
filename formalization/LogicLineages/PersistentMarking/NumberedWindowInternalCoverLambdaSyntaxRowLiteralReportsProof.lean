module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeKeyChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalSquareRootArithmeticSupportProof (strictTrans)
open NumberedWindowInternalAuxExchangeKeyChecks (exact_OpenRawConsBounds)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxMeasureStepTargets (childAt)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

structure LiteralReports (body : Positive (Fin 1)) (Γ : List (Formula α))
    (ty q old : OTerm α) : Prop where
  key : Nonempty (Derivation body Γ (programGraph currentKey (suc (lambdaPrior ty q)) (lambdaTape ty q old)))
  shape : Nonempty (Derivation body Γ (programGraph lambdaShape (suc z) (lambdaTape ty q old)))
  annotation : Nonempty (Derivation body Γ (programGraph (childAt 0) ty (lambdaTape ty q old)))
  child : Nonempty (Derivation body Γ (programGraph (childAt 1) q (lambdaTape ty q old)))
  earlier : Nonempty (Derivation body Γ (ltF q (suc (lambdaPrior ty q))))

theorem literalReports (ty q old : OTerm α) : LiteralReports body Γ ty q old := by
  let prior := lambdaPrior ty q
  let n := lambdaTerm ty q
  let xs := lambdaTape ty q old
  have key : Nonempty (Derivation body Γ (programGraph currentKey n xs)) :=
    unaryGraph .succ (.projection 0) n prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have tag : Nonempty (Derivation body Γ (unary (literal 1 2) (numeral 2) n)) :=
    literalGraph 2 ![n]
  obtain ⟨shape,fields⟩ := packedNode (literal 1 2) (numeral 2) [ty,q] tag
  let trail := rawCons q z
  let fieldsCode := rawCons ty trail
  have smaller : Nonempty (Derivation body Γ (ltF q n)) :=
    strictTrans q fieldsCode n
      (strictTrans q trail fieldsCode (exact_OpenRawConsBounds body α Γ q z).1
        (exact_OpenRawConsBounds body α Γ ty trail).2)
      (exact_OpenRawConsBounds body α Γ (numeral 2) fieldsCode).2
  exact ⟨key,unaryGraph (header 2 2) currentKey (suc z) n xs shape key,
    unaryGraph (field 0) currentKey ty n xs fields.1 key,
    unaryGraph (field 1) currentKey q n xs fields.2.1 key,smaller⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof
