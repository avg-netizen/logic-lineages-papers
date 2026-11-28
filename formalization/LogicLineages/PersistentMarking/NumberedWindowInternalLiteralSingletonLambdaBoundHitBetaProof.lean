module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaOperandAlignmentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaOpenCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenHitProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenAboveExistenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBoundHitBetaProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename packedBodyRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)
open NumberedWindowInternalLiteralBetaOperandAlignmentProof (AlignedBetaRow)
open NumberedWindowInternalLiteralSingletonDepthNumericProof (zeroDepthInstance)
open NumberedWindowInternalLiteralSingletonBoundMachineProof (singletonBound)
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof (boundTerm)
open NumberedWindowInternalLiteralSingletonBoundOpenHitProof (exact_OpenSingletonBoundAtPositiveDepth)
open NumberedWindowInternalLiteralSingletonBoundOpenAboveExistenceProof (boundTermRename)
open NumberedWindowInternalLiteralSingletonBetaInstallationProof (exact_OpenZeroDepthInstance)
open NumberedWindowInternalLiteralSingletonLambdaMachineProof (singletonLambda)
open NumberedWindowInternalLiteralSingletonLambdaOpenRowsProof (exact_OpenBetaLambdaBody)
open NumberedWindowInternalLiteralSingletonLambdaOpenCasesProof (exact_OpenSingletonLambdaRowZero)
open NumberedWindowInternalLiteralSingletonLambdaBetaTransportProof (exact_OpenInstanceBodyTransport)

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

/-- Accepted beta target at the discharged index under one binder, for
an arbitrary shift program and an arbitrary guarded replacement. The
leaf's instance graph has output `suc r`; the continuation receives an
object term `u` with the actual graph of `H` at output `suc u` and the
target equation. A zero output of `H` is refuted by functionality of the
same instance graph, so no nonzero law and no numeric fit of `H` is used. -/
theorem exact_OpenBetaLambdaBoundHitTarget (V : Program 1) (H : Program 2) (W : Program 3)
    (a body lamTy t r : OTerm α) (goal : Formula α)
    (inserted : D B Γ (unary V (suc z) a))
    (lambdaNode : D B Γ (unary V (suc z) (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (boundNode : D B Γ (unary V (suc z) (boundTerm t (suc z))))
    (shape : D B Γ (eqn body (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (held : D B Γ (programGraph (zeroDepthInstance (singletonLambda V H (singletonBound V H W)))
      (suc r) ![a,body]))
    (use : ∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (u : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      D B Δ (programGraph H (suc u) ![a.relabel ρ,suc z]) →
      D B Δ (eqn (suc (r.relabel ρ)) (suc (rawLambdaTerm (lamTy.relabel ρ) u))) →
      D B Δ (goal.relabel ρ)) : D B Γ goal := by
  let I := zeroDepthInstance (singletonLambda V H (singletonBound V H W))
  have canonical : D B Γ (programGraph I (suc r)
      ![a,rawLambdaTerm lamTy (boundTerm t (suc z))]) :=
    exact_OpenInstanceBodyTransport I (suc r) a body
      (rawLambdaTerm lamTy (boundTerm t (suc z))) shape held
  have transport : ∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      D B Δ (unary V (suc z) (a.relabel ρ)) ∧
      D B Δ (unary V (suc z)
        (rawLambdaTerm (lamTy.relabel ρ) (boundTerm (t.relabel ρ) (suc z)))) ∧
      D B Δ (unary V (suc z) (boundTerm (t.relabel ρ) (suc z))) ∧
      D B Δ (programGraph I (suc (r.relabel ρ))
        ![a.relabel ρ,rawLambdaTerm (lamTy.relabel ρ) (boundTerm (t.relabel ρ) (suc z))]) := by
    intro β ρ Δ keep
    refine ⟨?_,?_,?_,?_⟩
    · have moved := renameInto inserted ρ Δ keep
      rw [unaryRename,sucRelabel,zRelabel] at moved
      exact moved
    · have moved := renameInto lambdaNode ρ Δ keep
      rw [unaryRename,sucRelabel,zRelabel,rawLambdaTermRename,boundTermRename,
        sucRelabel,zRelabel] at moved
      exact moved
    · have moved := renameInto boundNode ρ Δ keep
      rw [unaryRename,sucRelabel,zRelabel,boundTermRename,sucRelabel,zRelabel] at moved
      exact moved
    · have moved := renameInto canonical ρ Δ keep
      rw [programRename,binaryInputsRename,sucRelabel,rawLambdaTermRename,boundTermRename,
        sucRelabel,zRelabel] at moved
      exact moved
  apply optionGraphCases H (![a,suc z] : Fin 2 → OTerm α) goal
  · intro β ρ Δ keep failed
    rw [binaryInputsRename,sucRelabel,zRelabel] at failed
    obtain ⟨inserted',lambdaNode',boundNode',moved⟩ := transport β ρ Δ keep
    have child := exact_OpenSingletonBoundAtPositiveDepth V H W (a.relabel ρ) z (t.relabel ρ) z
      inserted' boundNode' failed
    have row := exact_OpenSingletonLambdaRowZero V H (singletonBound V H W) (a.relabel ρ) z
      (lamTy.relabel ρ) (boundTerm (t.relabel ρ) (suc z)) inserted' lambdaNode' child
    have inst := exact_OpenZeroDepthInstance (singletonLambda V H (singletonBound V H W))
      (a.relabel ρ) (rawLambdaTerm (lamTy.relabel ρ) (boundTerm (t.relabel ρ) (suc z))) z row
    obtain ⟨same⟩ := valueUnique I (suc (r.relabel ρ)) z
      ![a.relabel ρ,rawLambdaTerm (lamTy.relabel ρ) (boundTerm (t.relabel ρ) (suc z))] moved inst
    exact ⟨Derivation.explosion (sucNeZeroApply same)⟩
  · intro β ρ Δ u keep hit
    rw [binaryInputsRename,sucRelabel,zRelabel] at hit
    obtain ⟨inserted',lambdaNode',boundNode',moved⟩ := transport β ρ Δ keep
    have child := exact_OpenSingletonBoundAtPositiveDepth V H W (a.relabel ρ) z (t.relabel ρ)
      (suc u) inserted' boundNode' hit
    have inst := exact_OpenBetaLambdaBody V H (singletonBound V H W) (a.relabel ρ)
      (lamTy.relabel ρ) (boundTerm (t.relabel ρ) (suc z)) u inserted' lambdaNode' child
    exact use β ρ Δ u keep hit
      (valueUnique I (suc (r.relabel ρ)) (suc (rawLambdaTerm (lamTy.relabel ρ) u))
        ![a.relabel ρ,rawLambdaTerm (lamTy.relabel ρ) (boundTerm (t.relabel ρ) (suc z))]
        moved inst)

/-- The same statement read from an aligned beta row: the held graph is
the row's own `instanceRun`. -/
theorem exact_OpenAlignedBetaLambdaBoundHit (L₀ L : Program 3)
    (V : Program 1) (H : Program 2) (W : Program 3)
    (ctx dom cod fn arg sc st after q r d e f a bind body y lamTy t : OTerm α) (goal : Formula α)
    (row : AlignedBetaRow L₀ L (zeroDepthInstance (singletonLambda V H (singletonBound V H W)))
      B Γ ctx dom cod fn arg sc st after q r d e f a bind body y)
    (inserted : D B Γ (unary V (suc z) a))
    (lambdaNode : D B Γ (unary V (suc z) (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (boundNode : D B Γ (unary V (suc z) (boundTerm t (suc z))))
    (shape : D B Γ (eqn body (rawLambdaTerm lamTy (boundTerm t (suc z)))))
    (use : ∀ (β : Type) (ρ : α → β) (Δ : List (Formula β)) (u : OTerm β),
      (∀ f ∈ Γ, f.relabel ρ ∈ Δ) →
      D B Δ (programGraph H (suc u) ![a.relabel ρ,suc z]) →
      D B Δ (eqn (suc (r.relabel ρ)) (suc (rawLambdaTerm (lamTy.relabel ρ) u))) →
      D B Δ (goal.relabel ρ)) : D B Γ goal :=
  exact_OpenBetaLambdaBoundHitTarget V H W a body lamTy t r goal inserted lambdaNode boundNode
    shape row.instanceRun use

#print axioms exact_OpenBetaLambdaBoundHitTarget
#print axioms exact_OpenAlignedBetaLambdaBoundHit
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonLambdaBoundHitBetaProof
