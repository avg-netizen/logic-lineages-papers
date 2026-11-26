module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixOwnExecutionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTickIterationFixedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixBypassProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename headTransport zeroSuccessorCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalNumericIterationSupportProof (repeatZeroValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (emitGraph)
open NumberedWindowInternalSparseRawRunSuccessProof (headRead)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralLambdaPrefixMachineProof
open NumberedWindowInternalLiteralLambdaPrefixFrameOpenProof
open NumberedWindowInternalLiteralLambdaPrefixLiveOpenProof (bit5)
open NumberedWindowInternalLiteralLambdaPrefixFirstOpenProof (exact_OpenPrefixOwnFlag)
open NumberedWindowInternalLiteralLambdaPrefixScopeProof (fiveInputsRename)
open NumberedWindowInternalLiteralTickIterationProof (shiftLate)
open NumberedWindowInternalLiteralTickIterationFixedProof (exact_OpenTickIterationFixed)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenPrefixStops (W : Program 3) (c t q w r : OTerm α)
    (off : D B Γ (programGraph isLambdaPrefix z ![c,t,q,w,r])) :
    D B Γ (bit5 (prefixOwn W) ![c,t,q,w,r]) := by
  let start := prefixStartTerm c t q w r
  let goal := bit5 (prefixOwn W) ![c,t,q,w,r]
  apply zeroSuccessorCases Γ w goal
  · let Δ := eqn w z :: Γ
    have base : D B Δ (programGraph (prefixLoop W) start ![z,start]) :=
      repeatZeroValue (prefixTick W) start
    have moved := headTransport (prefixLoop W) start z w ![start] ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ base
    exact exact_OpenPrefixOwnFlag W (suc z) (prefixFrameTerm c t q w r) c t q w r moved
  · intro β j Δ n keep wEq
    simp only [goal,bit5,programRename,fiveInputsRename,sucRelabel,zRelabel]
    let c' := c.relabel j
    let t' := t.relabel j
    let q' := q.relabel j
    let w' := w.relabel j
    let r' := r.relabel j
    let xs : Fin 5 → OTerm β := ![c',t',q',w',r']
    let old := prefixStartTerm c' t' q' w' r'
    let ready : OTerm β := stateTerm (suc z) z
    have readOff := renameInto off j Δ keep
    simp only [programRename,fiveInputsRename,zRelabel] at readOff
    have happy : D B Δ (programGraph prefixAccept ready xs) :=
      emitGraph _ _ (suc z) z xs (oneConstantValue xs) (constantZeroValue xs)
    have live : D B Δ (programGraph (prefixLive W) ready xs) :=
      zeroBranchIntro isLambdaPrefix prefixAccept _ ready xs readOff happy
    have tick := exact_OpenPrefixTickAtFrame W (suc z) c' t' q' w' r' ready live
    have fixed : D B Δ (programGraph (prefixLoop W) ready ![n,ready]) :=
      exact_OpenTickIterationFixed (prefixTick W) ready n (exact_OpenPrefixTickTerminal W (suc z))
    have last := shiftLate (prefixTick W) old ready n ready tick fixed
    have full := headTransport (prefixLoop W) ready (suc n) w' ![old] (wEq.map symm) last
    exact exact_OpenPrefixOwnFlag W (suc z) z c' t' q' w' r' full

#print axioms exact_OpenPrefixStops
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixBypassProof
