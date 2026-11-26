module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassRawSourceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileNeutralSourceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralReportedAuxiliaryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawGuardOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDecoratedCertifiedCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceSyntaxProof (fieldsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalLiteralAuxRootLeafFieldsProof (rawBottom)
open NumberedWindowInternalLiteralCoveredTypedAuxCasesProof (ActiveRaw)
open NumberedWindowInternalLiteralFunctionGuardInversionProof (Parts)
open NumberedWindowInternalLiteralCoveredNonLambdaAuxProof (exact_OpenCoveredNonLambdaAuxiliary)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow)
open NumberedWindowInternalLiteralCoveredMemoAuxRowProof (childAtWindow)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget targetGate)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralAtomicRawGuardOpenProof (exact_OpenLiteralAtomicRawUnderlying)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast atomicTest)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D exact_OpenAtomicLeastReport)
open NumberedWindowInternalLiteralAtomicLeastShapeProof
  (bottomAtom queryAtInput exact_OpenLiteralAtomicGuardedLeastSingleton)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralHeaderLeastOpenProof (exact_OpenLiteralHeaderLeastReport)
open NumberedWindowInternalLiteralAuxProfileLeastProof (auxProfileLeast)
open NumberedWindowInternalLiteralAuxProfileNeutralSourceProof (lambdaAt exact_OpenAuxiliarySourceFromSharedProfile)
open NumberedWindowInternalLiteralReportedAuxiliaryProof (leastRawMove)

open NumberedWindowInternalLiteralApplicationLeastDecoratorProof (auxiliaryDecorator)
open NumberedWindowInternalLiteralAuxClassRawSourceProof (exact_OpenAuxClassStackReport)
open NumberedWindowInternalLiteralAuxClassLeastOpenProof (exact_OpenLiteralAuxClassLeastReport)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The three physical least guards retain the same actual selected
value when opened, so its inner field comparisons are available
without changing the accepted AST. -/
theorem exact_OpenDecoratedAuxProfileFromStack (L : Program 3) (ctx ty q k : OTerm α)
    (h : D B Γ (programGraph (guardedLeast (headerLeast (auxiliaryDecorator L))) (suc k) ![ctx,ty,q])) :
    D B Γ (programGraph (auxProfileLeast L) (suc k) ![ctx,ty,q]) := by
  have cls := exact_OpenAuxClassStackReport L ctx ty q k h
  obtain ⟨test⟩ := exact_OpenLiteralAuxClassLeastReport (auxProfileLeast L) ctx ty q k cls
  exact ⟨Derivation.conjunctionLeft test⟩

/-- At a certified direct raw hop, the output of a non-lambda
application supplies the two shape hypotheses of the original raw
case splitter. Bottom is already the exact selected destination;
the alternative retains the genuine child raw call and its domains. -/
theorem exact_OpenDecoratedCertifiedAuxBottomOrChild
    (C : Program 3) (X : Program 2) (s : Settings)
    (leaf : Nat → Program 3) (other : Program 3) (base : Program 2) (T V i cv tv : Program 1)
    (L₀ : Program 3) (ctx ty dom cod fn arg before cert after q w r h : OTerm α)
    (goal : Formula α) :
    let W := coveredMemoWindow C s base T V
    let raw := ActiveRaw C s leaf other base T V
    let L := guardedLeast (headerLeast (auxiliaryDecorator L₀))
    let R := rawWithTarget i cv tv (guardedRaw raw) L
    D B Γ (programGraph L (suc before) ![ctx,ty,auxiliaryTerm dom cod fn arg]) →
    D B Γ (unary cellHead h fn) → D B Γ (lambdaAt h) →
    D B Γ (hopCalls R L ctx ty before cert after q w r) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (after.relabel j) (rawBottom (ty.relabel j))) → D B Δ (goal.relabel j)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (d e f a child d' e' g a' : OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      Parts B Δ (q.relabel j) (w.relabel j) (r.relabel j) d e f a child d' e' g a' →
      D B Δ (programGraph raw (suc z) ![ctx.relabel j,rawCons d e,f,child,g] ⊓
        (childAtWindow W V (ctx.relabel j) d a ⊓
          (hasLeast C X W s (ctx.relabel j) (rawCons d e) f ⊓
            (hasLeast C X W s (ctx.relabel j) (rawCons d e) g ⊓
              hasLeast C X W s (ctx.relabel j) d a)))) →
      D B Δ (hopCalls R L (ctx.relabel j) (ty.relabel j) (before.relabel j) (cert.relabel j)
        (after.relabel j) (q.relabel j) (w.relabel j) (r.relabel j)) →
      D B Δ (goal.relabel j)) → D B Γ goal := by
  intro W raw L R app head notL checked bottom child
  obtain ⟨report⟩ := checked
  let calls := Derivation.conjunctionRight report
  let value := Derivation.conjunctionRight calls
  have seed := exact_OpenDecoratedAuxProfileFromStack L₀ ctx ty (auxiliaryTerm dom cod fn arg) before app
  have actual := exact_OpenDecoratedAuxProfileFromStack L₀ ctx ty q before ⟨Derivation.conjunctionLeft value⟩
  obtain ⟨shape⟩ := exact_OpenAuxiliarySourceFromSharedProfile L₀ ctx ty dom cod fn arg q w r before h
    seed actual head notL
  let args : Fin 5 → OTerm α := ![ctx,ty,q,w,r]
  obtain ⟨step⟩ := conjunctionRecover (guardedRaw raw) (targetGate i cv tv L) args
    ⟨Derivation.conjunctionLeft calls⟩
  have unwrapped := exact_OpenLiteralAtomicRawUnderlying raw args ⟨Derivation.conjunctionLeft step⟩
  apply exact_OpenCoveredNonLambdaAuxiliary C X s leaf other base T V ctx ty q w r goal
    ⟨Derivation.conjunctionLeft shape⟩ ⟨Derivation.conjunctionRight shape⟩ unwrapped
  · intro β j Δ keep target
    have held := renameInto (⟨report⟩ : D B Γ (hopCalls R L ctx ty before cert after q w r)) j Δ keep
    rw [fieldsRename] at held
    obtain ⟨row⟩ := held
    let selected := Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight row))
    let sc := ctx.relabel j
    let st := ty.relabel j
    let rr := rawBottom st
    let kk := after.relabel j
    have onBottom := leastRawMove L sc st (r.relabel j) rr (suc kk) target ⟨selected⟩
    have atom : D B Δ (unary atomicTest (suc z) rr) := bottomAtom st
    obtain ⟨e⟩ := exact_OpenLiteralAtomicGuardedLeastSingleton (headerLeast (auxiliaryDecorator L₀))
      sc st rr kk onBottom (queryAtInput rr kk atom)
    exact bottom β j Δ keep ⟨symm e⟩
  · intro _ β j Δ d e f a w' d' e' g a' keep fields projected
    have held := renameInto (⟨report⟩ : D B Γ (hopCalls R L ctx ty before cert after q w r)) j Δ keep
    rw [fieldsRename] at held
    exact child β j Δ d e f a w' d' e' g a' keep fields projected held

#print axioms exact_OpenDecoratedAuxProfileFromStack
#print axioms exact_OpenDecoratedCertifiedAuxBottomOrChild
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDecoratedCertifiedCasesProof
