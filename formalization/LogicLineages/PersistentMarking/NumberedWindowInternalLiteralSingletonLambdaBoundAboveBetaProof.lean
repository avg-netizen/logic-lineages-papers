module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBoundAboveProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBoundAboveBetaProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename packedBodyRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralBetaLeafOpenProof
  (rawLambdaTerm BetaCalls exact_OpenBetaInstanceFromSelectors)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (zeroDepthInstance)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (singletonBound)
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof (boundTerm)
open NumberedWindowInternalLiteralSingletonBetaInstallationProof (exact_OpenZeroDepthInstance)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda)
open NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof (exact_OpenInstanceBodyTransport)
open NumberedWindowInternalLiteralSingletonBoundOpenAboveExistenceProof (boundTermRename)
open NumberedWindowInternalLiteralSingletonLambdaBoundAboveProof (exact_OpenSingletonLambdaBoundAbove)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem numeralRename {β : Type} (n : Nat) (ρ : α → β) :
    (numeral n : OTerm α).relabel ρ = numeral n := by
  induction n with
  | zero => exact zRelabel ρ
  | succ n ih =>
    simpa only [numeral,sucRelabel] using
      congrArg ID1Completion.InternalTagArithmeticSyntaxProof.suc ih

private theorem rawLambdaTermRename {β : Type} (ty b : OTerm α) (ρ : α → β) :
    (rawLambdaTerm ty b).relabel ρ = rawLambdaTerm (ty.relabel ρ) (b.relabel ρ) := by
  simp only [rawLambdaTerm,rawConsRename,numeralRename,packedBodyRename,List.map_cons,List.map_nil]

/-- Beta instance graph. At literal depth zero the installed program on a
lambda whose body is a bound variable above depth one returns the rebuilt
node with the lowered index. The zero depth is supplied by the instance
wrapper; the child comparison is the derivation of `1 < i`. -/
theorem exact_OpenBetaLambdaBoundAbove (V : Program 1) (H : Program 2) (W : Program 3)
    (a ty t i : OTerm α) (goal : Formula α)
    (inserted : D B Γ (unary V (suc z) a))
    (lambdaNode : D B Γ (unary V (suc z) (rawLambdaTerm ty (boundTerm t i))))
    (boundNode : D B Γ (unary V (suc z) (boundTerm t i)))
    (above : D B Γ (ltF (suc z) i))
    (use : ∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (j : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      D B Δ (eqn (i.relabel ρ) (suc j)) →
      D B Δ (programGraph (zeroDepthInstance (singletonLambda V H (singletonBound V H W)))
        (suc (rawLambdaTerm (ty.relabel ρ) (boundTerm (t.relabel ρ) j)))
        ![a.relabel ρ,rawLambdaTerm (ty.relabel ρ) (boundTerm (t.relabel ρ) (i.relabel ρ))]) →
      D B Δ (goal.relabel ρ)) : D B Γ goal := by
  apply exact_OpenSingletonLambdaBoundAbove V H W a z ty t i goal
    inserted lambdaNode boundNode above
  intro β ρ Δ j keep same run
  rw [zRelabel] at run
  exact use β ρ Δ j keep same
    (exact_OpenZeroDepthInstance (singletonLambda V H (singletonBound V H W)) (a.relabel ρ)
      (rawLambdaTerm (ty.relabel ρ) (boundTerm (t.relabel ρ) (i.relabel ρ)))
      (suc (rawLambdaTerm (ty.relabel ρ) (boundTerm (t.relabel ρ) j))) run)

/-- Accepted beta target. The beta leaf supplies a graph of its instance
program at an abstract body with output `suc r`. When that body is derivably
a lambda over a bound variable above depth one, the accepted target is the
rebuilt node with the lowered index, by functionality of the same graph. -/
theorem exact_OpenBetaLambdaBoundAboveTarget (V : Program 1) (H : Program 2) (W : Program 3)
    (a body ty t i r : OTerm α) (goal : Formula α)
    (inserted : D B Γ (unary V (suc z) a))
    (lambdaNode : D B Γ (unary V (suc z) (rawLambdaTerm ty (boundTerm t i))))
    (boundNode : D B Γ (unary V (suc z) (boundTerm t i)))
    (shape : D B Γ (eqn body (rawLambdaTerm ty (boundTerm t i))))
    (above : D B Γ (ltF (suc z) i))
    (held : D B Γ (programGraph (zeroDepthInstance (singletonLambda V H (singletonBound V H W)))
      (suc r) ![a,body]))
    (use : ∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (j : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      D B Δ (eqn (i.relabel ρ) (suc j)) →
      D B Δ (eqn (suc (r.relabel ρ))
        (suc (rawLambdaTerm (ty.relabel ρ) (boundTerm (t.relabel ρ) j)))) →
      D B Δ (goal.relabel ρ)) : D B Γ goal := by
  have canonical := exact_OpenInstanceBodyTransport
    (zeroDepthInstance (singletonLambda V H (singletonBound V H W))) (suc r) a body
    (rawLambdaTerm ty (boundTerm t i)) shape held
  apply exact_OpenBetaLambdaBoundAbove V H W a ty t i goal inserted lambdaNode boundNode above
  intro β ρ Δ j keep same run
  have moved := renameInto canonical ρ Δ keep
  rw [programRename,binaryInputsRename,sucRelabel,rawLambdaTermRename,boundTermRename] at moved
  exact use β ρ Δ j keep same
    (valueUnique (zeroDepthInstance (singletonLambda V H (singletonBound V H W)))
      (suc (r.relabel ρ)) (suc (rawLambdaTerm (ty.relabel ρ) (boundTerm (t.relabel ρ) j)))
      ![a.relabel ρ,rawLambdaTerm (ty.relabel ρ) (boundTerm (t.relabel ρ) (i.relabel ρ))]
      moved run)

/-- The same statement at the actual beta leaf: the instance graph is read
from the accepted leaf calls and the literal frame selectors. -/
theorem exact_OpenBetaLeafLambdaBoundAbove (V : Program 1) (H : Program 2) (W : Program 3)
    (q w r dom fn arg bind body ty t i : OTerm α) (goal : Formula α)
    (calls : BetaCalls B Γ (zeroDepthInstance (singletonLambda V H (singletonBound V H W))) q w r)
    (domRead : D B Γ (unary (field 0) dom q)) (fnRead : D B Γ (unary (field 2) fn q))
    (argRead : D B Γ (unary (field 3) arg q)) (bindRead : D B Γ (unary (field 0) bind fn))
    (bodyRead : D B Γ (unary (field 1) body fn))
    (inserted : D B Γ (unary V (suc z) arg))
    (lambdaNode : D B Γ (unary V (suc z) (rawLambdaTerm ty (boundTerm t i))))
    (boundNode : D B Γ (unary V (suc z) (boundTerm t i)))
    (shape : D B Γ (eqn body (rawLambdaTerm ty (boundTerm t i))))
    (above : D B Γ (ltF (suc z) i))
    (use : ∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (j : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      D B Δ (eqn (i.relabel ρ) (suc j)) →
      D B Δ (eqn (suc (r.relabel ρ))
        (suc (rawLambdaTerm (ty.relabel ρ) (boundTerm (t.relabel ρ) j)))) →
      D B Δ (goal.relabel ρ)) : D B Γ goal :=
  exact_OpenBetaLambdaBoundAboveTarget V H W arg body ty t i r goal inserted lambdaNode boundNode
    shape above
    (exact_OpenBetaInstanceFromSelectors
      (zeroDepthInstance (singletonLambda V H (singletonBound V H W)))
      q w r dom fn arg bind body calls domRead fnRead argRead bindRead bodyRead).2
    use

#print axioms exact_OpenBetaLambdaBoundAbove
#print axioms exact_OpenBetaLambdaBoundAboveTarget
#print axioms exact_OpenBetaLeafLambdaBoundAbove
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBoundAboveBetaProof
