module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundCoherenceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBaseCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundGuardIntroProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue outputTransport)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn)
open ID1Completion.InternalTagArithmeticSupportProof (congSuc symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (grammarTypeAt)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw leafTypeTest)
open NumberedWindowInternalCoverLexicalSlotTargets (slotCheck)
open NumberedWindowInternalCoverLexicalBoundWindowTargets (lexicalGuard)
open NumberedWindowInternalCoverNamedResultTargets (storedTypeResult)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof (exact_OpenCoverNamedLeafIntrinsicShape)
open NumberedWindowInternalCoverLambdaLexicalBaseCutProof (liftRawReport)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem introduceBoundGrammarGuard (s : Settings) (ctx ty i : OTerm α)
    (member : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty))) :
    Nonempty (Derivation body Γ (programGraph (onRaw (leafTypeTest s)) (suc z) ![ctx,namedTerm 1 ty i])) := by
  let code := Encodable.encode s.types
  let raw := namedTerm 1 ty i
  have finite : Nonempty (Derivation body Γ (unary (grammarTypeAt s) (suc z) ty)) := by
    apply compositionValue scratchMember ![literal 1 code,.projection 0]
      (suc z) ![ty] ![numeral code,ty] member
    intro j
    exact Fin.cases (literalGraph code ![ty])
      (Fin.cases (projectionValue 0 ![ty]) (fun l => Fin.elim0 l)) j
  have shape := exact_OpenCoverNamedLeafIntrinsicShape true body α Γ ty i
  have test : Nonempty (Derivation body Γ (unary (leafTypeTest s) (suc z) raw)) := by
    apply compositionValue (grammarTypeAt s) (fun _ : Fin 1 => field 0)
      (suc z) ![raw] ![ty] finite
    intro j
    obtain rfl := Fin.eq_zero j
    exact shape.2.2.2.1
  exact liftRawReport (leafTypeTest s) ctx raw (suc z) test

theorem introduceBoundLexicalGuard (ctx ty i : OTerm α)
    (slot : Nonempty (Derivation body Γ (programGraph slotCheck (suc z) ![i,ctx,ty]))) :
    Nonempty (Derivation body Γ (programGraph lexicalGuard (suc z) ![ctx,namedTerm 1 ty i])) := by
  let raw := namedTerm 1 ty i
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  have shape := exact_OpenCoverNamedLeafIntrinsicShape true body α Γ ty i
  apply compositionValue slotCheck ![onRaw (field 1),.projection 0,onRaw (field 0)]
    (suc z) xs ![i,ctx,ty] slot
  intro j
  exact Fin.cases (liftRawReport (field 1) ctx raw i shape.2.2.2.2.1)
    (Fin.cases (projectionValue 0 xs)
      (Fin.cases (liftRawReport (field 0) ctx raw ty shape.2.2.2.1) (fun l => Fin.elim0 l))) j

theorem introduceBoundStoredResult (ctx ty i result : OTerm α)
    (same : Nonempty (Derivation body Γ (eqn result ty))) :
    Nonempty (Derivation body Γ (programGraph storedTypeResult (suc result) ![ctx,namedTerm 1 ty i])) := by
  let raw := namedTerm 1 ty i
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  have shape := exact_OpenCoverNamedLeafIntrinsicShape true body α Γ ty i
  have actual : Nonempty (Derivation body Γ (programGraph storedTypeResult (suc ty) xs)) := by
    apply compositionValue .succ (fun _ : Fin 1 => onRaw (field 0)) (suc ty) xs ![ty] (successorValue ![ty])
    intro j
    obtain rfl := Fin.eq_zero j
    exact liftRawReport (field 0) ctx raw ty shape.2.2.2.1
  obtain ⟨eq⟩ := same
  exact outputTransport storedTypeResult (suc ty) (suc result) xs ⟨congSuc (symm eq)⟩ actual

#print axioms introduceBoundGrammarGuard
#print axioms introduceBoundLexicalGuard
#print axioms introduceBoundStoredResult

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundGuardIntroProof
