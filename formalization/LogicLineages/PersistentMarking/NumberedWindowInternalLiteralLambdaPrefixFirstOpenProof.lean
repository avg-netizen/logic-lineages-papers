module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixLiveOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTickIterationFixedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixFirstOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue headTransport projectionValue valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm sucNeZeroApply)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawRunSuccessProof (headRead)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralLambdaPrefixMachineProof
open NumberedWindowInternalLiteralLambdaPrefixFrameOpenProof
open NumberedWindowInternalLiteralLambdaPrefixLiveOpenProof
open NumberedWindowInternalLiteralTickIterationProof (shiftLate)
open NumberedWindowInternalLiteralTickIterationFixedProof (exact_OpenTickIterationFixed)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenPrefixOwnStateValue (W : Program 3) (out c t q w r : OTerm α)
    (run : D B Γ (programGraph (prefixLoop W) out ![w,prefixStartTerm c t q w r])) :
    D B Γ (programGraph (prefixOwnState W) out ![c,t,q,w,r]) := by
  let xs : Fin 5 → OTerm α := ![c,t,q,w,r]
  apply compositionValue (prefixLoop W) ![.projection 3,prefixStart] out xs ![w,prefixStartTerm c t q w r] run
  intro i
  exact Fin.cases (projectionValue 3 xs)
    (Fin.cases (exact_OpenPrefixStart c t q w r) (fun e => Fin.elim0 e)) i

theorem exact_OpenPrefixOwnFlag (W : Program 3) (flag frame c t q w r : OTerm α)
    (run : D B Γ (programGraph (prefixLoop W) (stateTerm flag frame) ![w,prefixStartTerm c t q w r])) :
    D B Γ (programGraph (prefixOwn W) flag ![c,t,q,w,r]) := by
  apply compositionValue cellHead (fun _ : Fin 1 => prefixOwnState W) flag ![c,t,q,w,r]
    ![stateTerm flag frame] (headRead flag frame)
  intro i
  obtain rfl := Fin.eq_zero i
  exact exact_OpenPrefixOwnStateValue W (stateTerm flag frame) c t q w r run

/-- For a positive original witness whose first raw frame is lambda,
success of the actual prefix loop physically entails validation of
both body windows. A failed first check persists at all later fuel. -/
theorem exact_OpenPrefixOwnFirstValidation (W : Program 3) (c t q w r n : OTerm α)
    (positive : D B Γ (eqn w (suc n)))
    (first : D B Γ (bit5 isLambdaPrefix ![c,t,q,w,r]))
    (checked : D B Γ (bit5 (prefixOwn W) ![c,t,q,w,r])) :
    D B Γ (bit5 (prefixValidation W) ![c,t,q,w,r]) := by
  let xs : Fin 5 → OTerm α := ![c,t,q,w,r]
  let F := bit5 (prefixValidation W) xs
  obtain ⟨a⟩ := positive
  obtain ⟨b⟩ := first
  obtain ⟨h⟩ := checked
  have no : D B (F.not :: Γ) F := by
    have invalid : D B (F.not :: Γ) (programGraph (prefixValidation W) z xs) :=
      conjunctionReject _ _ xs ⟨Derivation.hypothesis List.mem_cons_self⟩
    let start := prefixStartTerm c t q w r
    let bad : OTerm α := stateTerm z z
    have reject := exact_OpenPrefixRejects W c t q w r ⟨addHyp b _⟩ invalid
    have fixed := exact_OpenTickIterationFixed (body := B) (Γ := F.not :: Γ) (prefixTick W) bad n
      (exact_OpenPrefixTickTerminal W z)
    have late : D B (F.not :: Γ) (programGraph (prefixLoop W) bad ![suc n,start]) :=
      shiftLate (prefixTick W) start bad n bad reject fixed
    have atWitness := headTransport (prefixLoop W) bad (suc n) w ![start]
      ⟨symm (addHyp a _)⟩ late
    have zero := exact_OpenPrefixOwnFlag W z z c t q w r atWitness
    obtain ⟨bad⟩ := valueUnique (prefixOwn W) (suc z) z xs ⟨addHyp h _⟩ zero
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  exact ⟨disjunctionElimination (excludedMiddle F)
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))
    (Derivation.implicationIntroduction (Classical.choice no))⟩

#print axioms exact_OpenPrefixOwnStateValue
#print axioms exact_OpenPrefixOwnFlag
#print axioms exact_OpenPrefixOwnFirstValidation
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixFirstOpenProof
