module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictImageRetapeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRankForwardRowsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteCodomainProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictImageAlignmentProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm trans)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ChildClosed)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteScalar finiteCodes)
open NumberedWindowInternalLiteralFiniteCodomainProof (exact_OpenLiteralFiniteCodomain)
open NumberedWindowInternalLiteralAtomicAddressReportProof (rebuildAddress)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (fullAuxiliaryDecorator childGuardedLeast)
open NumberedWindowInternalLiteralStrictOperandMinimaProof (exact_OpenStrictCertificateOperandMinima)
open NumberedWindowInternalLiteralStrictForkRetapeProof (exact_OpenStrictRetapeContext exact_OpenStrictMemberRetape)
open NumberedWindowInternalLiteralStrictImageRetapeProof
open NumberedWindowInternalLiteralRankForwardRowsProof (OpenRankTypeGuards)
open NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof (ParentTypeEvidence)
open NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof (selectedBiAuxType exact_OpenBiAuxTypeEvidence)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

structure StrictImageAligned (s : Settings) (T TV : Program 1) (core : Program 3)
    (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (sc d e g a arg u y after : OTerm α) : Prop where
  types : ParentTypeEvidence s T TV B Γ d e
  argLeast : D B Γ (programGraph core (suc arg) ![sc,d,a])
  goalLeast : D B Γ (programGraph core (suc after) ![sc,e,auxiliaryTerm d e g a])
  argument : D B Γ (addressReport u sc d arg)
  result : D B Γ (eqn y (addressTerm sc e after))

/-- Recover every retained operand and result coordinate from the
genuine application and genuine hop, before the two class transports
which prove that the canonical image is precisely the old destination. -/
theorem exact_OpenStrictImageAlignment (s : Settings) (P : List ProbeTy) (closed : ChildClosed P)
    (cv tv T : Program 1) (W core : Program 3)
    (x u y ctx result dom cod fn arg sc st before after q r d e f a d' e' g a' : OTerm α) :
    let L := guardedLeast (headerLeast (fullAuxiliaryDecorator core))
    let i := finiteScalar (addressScalar cv tv W L) (finiteCodes P)
    let Tg := selectedBiAuxType s T tv
    OpenRankTypeGuards P Tg tv →
    D B Γ (unary i (suc z) x) → D B Γ (unary i (suc z) u) →
    D B Γ (parsedApplicationInputs x u ctx result dom cod fn arg) →
    D B Γ (addressReport y sc st after) →
    D B Γ (eqn sc ctx) → D B Γ (eqn st cod) →
    D B Γ (programGraph L (suc before) ![sc,st,auxiliaryTerm dom cod fn arg]) →
    D B Γ (programGraph L (suc before) ![sc,st,q]) →
    D B Γ (programGraph L (suc after) ![sc,st,r]) →
    D B Γ (eqn q (auxiliaryTerm d e f a)) → D B Γ (eqn r (auxiliaryTerm d' e' g a')) →
    D B Γ (eqn d d') → D B Γ (eqn e e') → D B Γ (eqn a a') →
    StrictImageAligned s Tg tv core B Γ sc d e g a arg u y after := by
  intro L i Tg openTy sx su parsed addr scope outTy app source target qRaw rRaw dd ee aa
  have sameApp := exact_OpenStrictRetapeContext L sc ctx st (auxiliaryTerm dom cod fn arg) (suc before) scope app
  have sameQ := exact_OpenStrictRetapeContext L sc ctx st q (suc before) scope source
  obtain ⟨arrow,domain,⟨domEq⟩,⟨codEq⟩,_,argClass⟩ :=
    exact_OpenStrictCertificateOperandMinima cv tv W core (finiteCodes P) x u ctx st result dom cod fn arg
      q d e f a before sx su parsed sameApp sameQ qRaw
  have codomain := exact_OpenLiteralFiniteCodomain P closed dom cod arrow
  have inD := exact_OpenStrictMemberRetape (finiteCodes P) dom d ⟨symm domEq⟩ domain
  have inE := exact_OpenStrictMemberRetape (finiteCodes P) cod e ⟨symm codEq⟩ codomain
  have types := exact_OpenBiAuxTypeEvidence s T tv d e (openTy B α Γ d inD).1 (openTy B α Γ e inE).1
  obtain ⟨scope⟩ := scope
  obtain ⟨outTy⟩ := outTy
  have childMin := exact_OpenStrictRetapeContext (childGuardedLeast core) ctx sc d a (suc arg) ⟨symm scope⟩ argClass
  have actualArg := exact_OpenStrictChildPrimitiveReport core sc d a arg childMin
  have outputType : D B Γ (eqn st e) := ⟨trans outTy (symm codEq)⟩
  have rendered := exact_OpenStrictApplicationTermRetape r d e g a d' e' a' rRaw dd ee aa
  have goalParent := exact_OpenStrictRetapeTypeAndRaw core sc st e r (auxiliaryTerm d e g a) (suc after)
    outputType rendered (exact_OpenStrictFullPrimitiveReport core sc st r after target)
  have realArg := exact_OpenStrictOriginalArgumentAddress x u ctx result dom cod fn arg sc d
    parsed ⟨symm scope⟩ ⟨symm domEq⟩
  have resultAddress := rebuildAddress y sc st after sc e after addr ⟨refl sc⟩ outputType ⟨refl after⟩
  exact ⟨types,actualArg,goalParent,realArg,resultAddress⟩

#print axioms exact_OpenStrictImageAlignment
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictImageAlignmentProof
