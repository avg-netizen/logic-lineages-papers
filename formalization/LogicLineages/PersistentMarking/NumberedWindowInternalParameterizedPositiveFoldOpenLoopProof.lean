module
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenConsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorIntroductionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenLoopProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue recursionZeroValue headTransport)
open ID1Completion.InternalRecursionGraphSuccessorIntroductionProof (recursionSuccessorIntroduction)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFold (initial)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (call6)
open NumberedWindowInternalParameterizedPositiveFold
open NumberedWindowInternalParameterizedPositiveFoldOpenConsProof

abbrev loopAt {α : Type} (A : Program 4) (out fuel c ty start cert : OTerm α) : Formula α :=
  programGraph (iterateAt A) out ![fuel,c,ty,start,cert]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenParameterizedLoopStart (A : Program 4)
    (state c ty start cert : OTerm α)
    (held : Nonempty (Derivation body Γ (scratchGraph state cert start))) :
    Nonempty (Derivation body Γ (loopAt A state z c ty start cert)) := by
  have init : Nonempty (Derivation body Γ (programGraph initial state ![c,ty,start,cert])) := by
    apply compositionValue consCode ![.projection 3,.projection 2] state ![c,ty,start,cert] ![cert,start] held
    intro i
    exact Fin.cases (projectionValue (3 : Fin 4) ![c,ty,start,cert])
      (Fin.cases (projectionValue (2 : Fin 4) ![c,ty,start,cert]) (fun k => Fin.elim0 k)) i
  exact recursionZeroValue initial (stepAt A) state ![c,ty,start,cert] init

theorem exact_OpenParameterizedLoopStep (A : Program 4)
    (out prior fuel c ty start cert cursor current hop tail next : OTerm α)
    (previous : Nonempty (Derivation body Γ (loopAt A prior fuel c ty start cert)))
    (before : Nonempty (Derivation body Γ (scratchGraph prior cursor current)))
    (owner : Nonempty (Derivation body Γ (consGraph cursor hop tail)))
    (actual : Nonempty (Derivation body Γ (programGraph A next ![c,ty,current,hop])))
    (after : Nonempty (Derivation body Γ (scratchGraph out tail next))) :
    Nonempty (Derivation body Γ (loopAt A out (suc fuel) c ty start cert)) :=
  recursionSuccessorIntroduction Γ (OrdinaryArithmetic.graphFormula initial)
    (OrdinaryArithmetic.graphFormula (stepAt A)) out fuel prior ![c,ty,start,cert] previous
    (exact_OpenParameterizedConsTransition A out fuel prior c ty start cert cursor current hop tail next
      before owner actual after)

theorem exact_OpenParameterizedLoopFuelTransport (A : Program 4)
    (state a b c ty start cert : OTerm α)
    (same : Nonempty (Derivation body Γ (eqn a b)))
    (known : Nonempty (Derivation body Γ (loopAt A state a c ty start cert))) :
    Nonempty (Derivation body Γ (loopAt A state b c ty start cert)) :=
  headTransport (iterateAt A) state a b ![c,ty,start,cert] same known

#print axioms exact_OpenParameterizedLoopStart
#print axioms exact_OpenParameterizedLoopStep
#print axioms exact_OpenParameterizedLoopFuelTransport
end LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenLoopProof
