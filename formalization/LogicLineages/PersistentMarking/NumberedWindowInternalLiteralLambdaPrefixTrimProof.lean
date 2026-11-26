module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixOwnExecutionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTickIterationFixedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFusionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixTrimProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport outputTransport valueUnique programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalNumericIteration (repeatGraph)
open ID1Completion.InternalNumericIterationFusionProof (fusionValue)
open ID1Completion.InternalNumericIterationSyntaxProof (repeatRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseRawRunShapeMotiveProof (pairRename)
open NumberedWindowInternalSparseRawRunSuccessProof (headRead)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralLambdaPrefixMachineProof
open NumberedWindowInternalLiteralLambdaPrefixFrameOpenProof (exact_OpenPrefixTickTerminal)
open NumberedWindowInternalLiteralLambdaPrefixLiveOpenProof (bit5)
open NumberedWindowInternalLiteralLambdaPrefixScopeProof (fiveInputsRename)
open NumberedWindowInternalLiteralLambdaPrefixSafetySyntaxProof
open NumberedWindowInternalLiteralLambdaPrefixSafetyLoopProof (exact_OpenPrefixLoopSafe)
open NumberedWindowInternalLiteralLambdaPrefixOwnExecutionProof
open NumberedWindowInternalLiteralTickIterationFixedProof (exact_OpenTickIterationFixed)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- An accepting run with any excess fuel certifies the child's actual
own-witness run. A rejected shorter run would force the same absorbing
zero state for the larger fuel, by composition of genuine recursions. -/
theorem exact_OpenTrimLambdaPrefix (W : Program 3) (c t q w r gap out : OTerm α)
    (held : D B Γ (repeatGraph (prefixTick W) out (add w gap) (prefixStartTerm c t q w r)))
    (head : D B Γ (unary cellHead (suc z) out)) :
    D B Γ (bit5 (prefixOwn W) ![c,t,q,w,r]) := by
  apply programCases (prefixLoop W) ![w,prefixStartTerm c t q w r] _
  intro β j Δ mid keep prior
  simp only [bit5,programRename,fiveInputsRename,sucRelabel,zRelabel]
  rw [pairRename,prefixStartTermRename] at prior
  let c' := c.relabel j
  let t' := t.relabel j
  let q' := q.relabel j
  let w' := w.relabel j
  let r' := r.relabel j
  let g := gap.relabel j
  let start := prefixStartTerm c' t' q' w' r'
  let P := unary cellHead (suc z) mid
  let R := eqn mid rejectedState
  let want := bit5 (prefixOwn W) ![c',t',q',w',r']
  have initial : D B Δ (prefixSafe start) :=
    oneStateSafe start (headRead (suc z) (prefixFrameTerm c' t' q' w' r'))
  obtain ⟨valid⟩ := exact_OpenPrefixLoopSafe W w' start mid initial prior
  obtain ⟨old⟩ := prior
  have known := renameInto held j Δ keep
  rw [repeatRename,addRelabel,prefixStartTermRename] at known
  obtain ⟨large⟩ := known
  have flag := renameInto head j Δ keep
  rw [unaryRename,sucRelabel,zRelabel] at flag
  obtain ⟨unit⟩ := flag
  have yes : D B (P :: Δ) want := exact_OpenPrefixOwnIntroduce W c' t' q' w' r' mid
    ⟨addHyp old P⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  have no : D B (R :: Δ) want := by
    have badFirst : D B (R :: Δ) (repeatGraph (prefixTick W) rejectedState w' start) :=
      outputTransport (prefixLoop W) mid rejectedState ![w',start]
        ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp old R⟩
    have badFixed : D B (R :: Δ) (repeatGraph (prefixTick W) rejectedState g rejectedState) :=
      exact_OpenTickIterationFixed (prefixTick W) rejectedState g (exact_OpenPrefixTickTerminal W z)
    have badLarge := fusionValue (prefixTick W) w' g start rejectedState rejectedState badFirst badFixed
    have eq := valueUnique (prefixLoop W) (out.relabel j) rejectedState ![add w' g,start]
      ⟨addHyp large R⟩ badLarge
    have wrong := headTransport cellHead (suc z) (out.relabel j) rejectedState Fin.elim0 eq ⟨addHyp unit R⟩
    obtain ⟨impossible⟩ := valueUnique cellHead (suc z) z ![rejectedState] wrong (headRead z z)
    exact ⟨Derivation.explosion (sucNeZeroApply impossible)⟩
  exact ⟨disjunctionElimination valid (Derivation.implicationIntroduction (Classical.choice yes))
    (Derivation.implicationIntroduction (Classical.choice no))⟩

#print axioms exact_OpenTrimLambdaPrefix
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixTrimProof
