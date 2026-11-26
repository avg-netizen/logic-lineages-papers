module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedEdgeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedBetaInstanceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictOperandMinimaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictForkRetapeProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaOperandAlignmentProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons suc z unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteScalar)
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (fullAuxiliaryDecorator childGuardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralStrictForkRetapeProof (exact_OpenStrictRetapeContext)
open NumberedWindowInternalLiteralStrictOperandMinimaProof (exact_OpenStrictCertificateOperandMinima)
open NumberedWindowInternalLiteralBetaLeafOpenProof (rawLambdaTerm)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

structure AlignedBetaRow (L₀ L : Program 3) (U : Program 2)
    (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (ctx dom cod fn arg sc st after q r d e f a bind body y : OTerm α) : Prop where
  source : D B Γ (eqn q (auxiliaryTerm d e f a))
  functionShape : D B Γ (eqn f (rawLambdaTerm bind body))
  binderType : D B Γ (eqn d bind)
  domain : D B Γ (eqn d dom)
  codomain : D B Γ (eqn e cod)
  functionClass : D B Γ (programGraph (childGuardedLeast L₀) (suc fn) ![ctx,rawCons d e,f])
  argumentClass : D B Γ (programGraph (childGuardedLeast L₀) (suc arg) ![ctx,d,a])
  instanceRun : D B Γ (programGraph U (suc r) ![a,body])
  targetClass : D B Γ (programGraph L (suc after) ![sc,st,r])
  targetAddress : D B Γ (addressReport y sc st after)

/-- The raw beta run is on the accepted function and argument
classes, not an unrelated lambda application with the same type.
Its target least and exact emitted address remain unchanged. -/
theorem exact_OpenAlignedBetaRow (cv tv : Program 1) (W L₀ : Program 3)
    (U : Program 2) (finite : List Nat)
    (x u y ctx result dom cod fn arg sc st before after q r d e f a bind body : OTerm α) :
    let L := guardedLeast (headerLeast (fullAuxiliaryDecorator L₀))
    let i := finiteScalar (addressScalar cv tv W L) finite
    D B Γ (unary i (suc z) x) → D B Γ (unary i (suc z) u) →
    D B Γ (parsedApplicationInputs x u ctx result dom cod fn arg) →
    D B Γ (eqn sc ctx) →
    D B Γ (programGraph L (suc before) ![sc,st,auxiliaryTerm dom cod fn arg]) →
    D B Γ (programGraph L (suc before) ![sc,st,q]) →
    D B Γ (eqn q (auxiliaryTerm d e f a)) → D B Γ (eqn f (rawLambdaTerm bind body)) →
    D B Γ (eqn d bind) → D B Γ (programGraph U (suc r) ![a,body]) →
    D B Γ (programGraph L (suc after) ![sc,st,r]) → D B Γ (addressReport y sc st after) →
    AlignedBetaRow L₀ L U B Γ ctx dom cod fn arg sc st after q r d e f a bind body y := by
  intro L i left right parsed same parent rawSource parts head binder computed target addr
  have parent' := exact_OpenStrictRetapeContext L sc ctx st (auxiliaryTerm dom cod fn arg) (suc before) same parent
  have source' := exact_OpenStrictRetapeContext L sc ctx st q (suc before) same rawSource
  obtain ⟨_,_,de,ce,fnReport,argReport⟩ :=
    exact_OpenStrictCertificateOperandMinima cv tv W L₀ finite x u ctx st result dom cod fn arg q d e f a before
      left right parsed parent' source' parts
  exact ⟨parts,head,binder,de,ce,fnReport,argReport,computed,target,addr⟩

#print axioms exact_OpenAlignedBetaRow
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaOperandAlignmentProof
