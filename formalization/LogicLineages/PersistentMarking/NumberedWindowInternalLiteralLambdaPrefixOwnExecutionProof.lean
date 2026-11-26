module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixSafetyLoopProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeMotiveProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixOwnExecutionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue programRename)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBodyRename)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseRawRunShapeMotiveProof (pairRename)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateRename)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralLambdaPrefixMachineProof
open NumberedWindowInternalLiteralLambdaPrefixLiveOpenProof (bit5)
open NumberedWindowInternalLiteralLambdaPrefixFirstOpenProof (exact_OpenPrefixOwnStateValue)
open NumberedWindowInternalLiteralLambdaPrefixScopeProof (movePrefixBit)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem prefixFrameTermRename {β : Type} (c t q w r : OTerm α) (j : α → β) :
    (prefixFrameTerm c t q w r).relabel j =
      prefixFrameTerm (c.relabel j) (t.relabel j) (q.relabel j) (w.relabel j) (r.relabel j) := by
  simp only [prefixFrameTerm,sucRelabel,packedBodyRename,List.map_cons,List.map_nil]

theorem prefixStartTermRename {β : Type} (c t q w r : OTerm α) (j : α → β) :
    (prefixStartTerm c t q w r).relabel j =
      prefixStartTerm (c.relabel j) (t.relabel j) (q.relabel j) (w.relabel j) (r.relabel j) := by
  simp only [prefixStartTerm,stateRename,sucRelabel,zRelabel,prefixFrameTermRename]

theorem exact_OpenPrefixOwnRead (W : Program 3) (c t q w r out : OTerm α)
    (held : D B Γ (bit5 (prefixOwn W) ![c,t,q,w,r]))
    (run : D B Γ (programGraph (prefixLoop W) out ![w,prefixStartTerm c t q w r])) :
    D B Γ (unary cellHead (suc z) out) := by
  apply compositionRecover cellHead (fun _ : Fin 1 => prefixOwnState W) (suc z) ![c,t,q,w,r] ![out] held
  intro i
  obtain rfl := Fin.eq_zero i
  exact exact_OpenPrefixOwnStateValue W out c t q w r run

theorem exact_OpenPrefixOwnIntroduce (W : Program 3) (c t q w r out : OTerm α)
    (run : D B Γ (programGraph (prefixLoop W) out ![w,prefixStartTerm c t q w r]))
    (good : D B Γ (unary cellHead (suc z) out)) :
    D B Γ (bit5 (prefixOwn W) ![c,t,q,w,r]) := by
  apply compositionValue cellHead (fun _ : Fin 1 => prefixOwnState W) (suc z) ![c,t,q,w,r] ![out] good
  intro i
  obtain rfl := Fin.eq_zero i
  exact exact_OpenPrefixOwnStateValue W out c t q w r run

theorem exact_OpenPrefixOwnExecution (W : Program 3) (c t q w r : OTerm α) (goal : Formula α)
    (held : D B Γ (bit5 (prefixOwn W) ![c,t,q,w,r]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (out : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (programGraph (prefixLoop W) out
        ![w.relabel j,prefixStartTerm (c.relabel j) (t.relabel j) (q.relabel j) (w.relabel j) (r.relabel j)]) →
      D B Δ (unary cellHead (suc z) out) → D B Δ (goal.relabel j)) : D B Γ goal := by
  apply programCases (prefixLoop W) ![w,prefixStartTerm c t q w r] goal
  intro β j Δ out keep run
  rw [pairRename,prefixStartTermRename] at run
  have here := movePrefixBit (prefixOwn W) c t q w r j Δ keep held
  exact use β j Δ out keep run
    (exact_OpenPrefixOwnRead W (c.relabel j) (t.relabel j) (q.relabel j) (w.relabel j) (r.relabel j) out here run)

#print axioms prefixStartTermRename
#print axioms exact_OpenPrefixOwnRead
#print axioms exact_OpenPrefixOwnIntroduce
#print axioms exact_OpenPrefixOwnExecution
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixOwnExecutionProof
