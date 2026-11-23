module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaRunTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftOwnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShiftProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaTickProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaProperExitConverseProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparseRawLambdaFrame (endpointTerm witnessTerm)
open NumberedWindowInternalSparseRawLambdaRun (lambdaFallback)
open NumberedWindowInternalSparseRawRun (iterateState ownRun)
open NumberedWindowInternalSparseRawTick (chosenTick)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawRunLiftOwnProof (initialTerm ownLoop)
open NumberedWindowInternalSparseRawRunSuccessProof (ownRunTerminal)
open NumberedWindowInternalSparseRawRunShiftProof (shiftEarly shiftLate)
open NumberedWindowInternalSparseRawLambdaTickProof (exact_OpenLambdaContextTick)
open NumberedWindowInternalSparseRawTickOpenChecks (exact_OpenLiftedTick)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev bodyTape (src child dst : OTerm α) : Fin 3 → OTerm α := ![src,child,dst]
abbrev fnTape (dom src child dst : OTerm α) : Fin 3 → OTerm α :=
  ![endpointTerm dom src,witnessTerm child,endpointTerm dom dst]
abbrev appliedTape (dom cod arg src child dst : OTerm α) : Fin 3 → OTerm α :=
  ![auxiliaryTerm dom cod (endpointTerm dom src) arg,
    functionWitnessTerm (witnessTerm child),
    auxiliaryTerm dom cod (endpointTerm dom dst) arg]

/-- Peel exactly the two real original ticks, at a held literal
tag5(tag1(child)), on the same open state machine and original output.
Residual fuel is arbitrary; no equality to child witness code claimed. -/
theorem exact_OpenLiteralLambdaProperResidual (root other : Program 3)
    (dom cod arg src child dst fuel out : OTerm α) :
    let Q := lambdaFallback other
    let a := initialTerm (appliedTape dom cod arg src child dst)
    let f := initialTerm (fnTape dom src child dst)
    let b := initialTerm (bodyTape src child dst)
    Nonempty (Derivation B Γ (programGraph (iterateState root Q) out ![suc (suc fuel),a])) ↔
    Nonempty (Derivation B Γ (programGraph (iterateState root Q) out ![fuel,b])) := by
  intro Q a f b
  obtain ⟨top⟩ := exact_OpenLiftedTick B root Q α z dom cod arg
    (endpointTerm dom src) (witnessTerm child) (endpointTerm dom dst)
  have first : Nonempty (Derivation B Γ (programGraph (chosenTick root Q) f ![a])) :=
    ⟨weakenClosed top Γ⟩
  have second : Nonempty (Derivation B Γ (programGraph (chosenTick root Q) b ![f])) :=
    exact_OpenLambdaContextTick B root other α Γ z dom src child dst
  constructor
  · intro accepted
    exact shiftEarly root Q f b fuel out second
      (shiftEarly root Q a f (suc fuel) out first accepted)
  · intro accepted
    exact shiftLate root Q a f (suc fuel) out first
      (shiftLate root Q f b fuel out second accepted)

/-- Specialize the exact converse to a genuinely accepted parent own
run. A supplied object equality exposes the parent's actual residual
fuel after the two ticks. This does not shorten it to child own fuel. -/
theorem exact_OpenLiteralLambdaProperOwnResidual (root other : Program 3)
    (dom cod arg src child dst fuel k : OTerm α)
    (fuelFit : Nonempty (Derivation B Γ
      (eqn (functionWitnessTerm (witnessTerm child)) (suc (suc fuel)))))
    (accepted : Nonempty (Derivation B Γ
      (programGraph (ownRun root (lambdaFallback other)) (suc k)
        (appliedTape dom cod arg src child dst)))) :
    Nonempty (Derivation B Γ (programGraph (iterateState root (lambdaFallback other))
      (stateTerm (suc k) z) ![fuel,initialTerm (bodyTape src child dst)])) := by
  let Q := lambdaFallback other
  let xs := appliedTape dom cod arg src child dst
  let out := stateTerm (suc k) z
  have terminal := ownRunTerminal root Q k xs accepted
  have actual := ownLoop root Q out xs terminal
  have exposed : Nonempty (Derivation B Γ
      (programGraph (iterateState root Q) out ![suc (suc fuel),initialTerm xs])) := by
    exact headTransport (iterateState root Q) out (functionWitnessTerm (witnessTerm child))
      (suc (suc fuel)) ![initialTerm xs] fuelFit actual
  exact (exact_OpenLiteralLambdaProperResidual root other dom cod arg src child dst fuel out).1 exposed

#print axioms exact_OpenLiteralLambdaProperResidual
#print axioms exact_OpenLiteralLambdaProperOwnResidual
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaProperExitConverseProof
