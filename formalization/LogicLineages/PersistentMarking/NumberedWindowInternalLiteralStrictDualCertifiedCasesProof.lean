module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictDualChildProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPerTickNonLambdaAuxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTypedGuardReturnProof
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictDualCertifiedCasesProof
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
open NumberedWindowInternalLiteralAtomicCoveredCasesProof (PerTickRaw)
open NumberedWindowInternalLiteralFunctionGuardInversionProof (Parts)
open NumberedWindowInternalLiteralPerTickNonLambdaAuxProof (exact_OpenPerTickNonLambdaAuxiliary)
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

open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (fullAuxiliaryDecorator childGuardedLeast)
open NumberedWindowInternalLiteralStrictDualChildProof (strictDualRaw exact_OpenStrictDualChild)
open NumberedWindowInternalLiteralDualTypedRawProof (exact_OpenDualTypedRawEndpoints)
open NumberedWindowInternalLiteralStrictSealedWindowProof (strictSealedWindow)
open NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof (windowRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalLiteralAuxCertifiedCasesProof (exact_OpenAuxProfileFromStack)
open NumberedWindowInternalLiteralAuxClassRawSourceProof (exact_OpenAuxClassStackReport)
open NumberedWindowInternalLiteralAuxClassLeastOpenProof (exact_OpenLiteralAuxClassLeastReport)

open NumberedWindowInternalLiteralRootDispatchNumericProof (root)
open NumberedWindowInternalLiteralAuxRootLeaf (leafAtAuxiliary)
open NumberedWindowInternalLiteralBoundedFallback (fallback)
open NumberedWindowInternalLiteralAuxiliaryAtomicTypedRawProof (exact_OpenLiteralAuxiliaryAtomicRawAtoms)
open NumberedWindowInternalLiteralAtomicTypedGuardReturnProof (exact_OpenLiteralRawGuardReturnFromAtoms)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The three physical least guards retain the same actual selected
value when opened, so its inner field comparisons are available
without changing the accepted AST. -/
theorem exact_OpenStrictDualAuxProfileFromStack (L : Program 3) (ctx ty q k : OTerm α)
    (h : D B Γ (programGraph (guardedLeast (headerLeast (fullAuxiliaryDecorator L))) (suc k) ![ctx,ty,q])) :
    D B Γ (programGraph (auxProfileLeast L) (suc k) ![ctx,ty,q]) := by
  obtain ⟨atom⟩ := exact_OpenAtomicLeastReport (headerLeast (fullAuxiliaryDecorator L)) ctx ty q k h
  obtain ⟨top⟩ := exact_OpenLiteralHeaderLeastReport (fullAuxiliaryDecorator L) ctx ty q k
    ⟨Derivation.conjunctionLeft atom⟩
  obtain ⟨classes⟩ := exact_OpenLiteralAuxClassLeastReport (childGuardedLeast L) ctx ty q k
    ⟨Derivation.conjunctionLeft top⟩
  exact exact_OpenAuxProfileFromStack L ctx ty q k ⟨Derivation.conjunctionLeft classes⟩

/-- At a certified direct raw hop, the output of a non-lambda
application supplies the two shape hypotheses of the original raw
case splitter. Bottom is already the exact selected destination;
the alternative retains the genuine child raw call and its domains. -/
theorem exact_OpenStrictDualCertifiedAuxBottomOrChild
    (C : Program 3) (X : Program 2) (s : Settings)
    (leaf : Nat → Program 3) (other : Program 3) (rawBase base : Program 2) (rawT V T i cv tv : Program 1)
    (L₀ : Program 3) (ctx ty dom cod fn arg before cert after q w r h : OTerm α)
    (goal : Formula α) :
    let W := coveredMemoWindow C s rawBase rawT V
    let Z := strictSealedWindow C s base T
    let raw := strictDualRaw C s leaf other rawBase base rawT V T
    let L := guardedLeast (headerLeast (fullAuxiliaryDecorator L₀))
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
      D B Δ (programGraph (guardedRaw raw) (suc z) ![ctx.relabel j,rawCons d e,f,child,g] ⊓
        (childAtWindow W V (ctx.relabel j) d a ⊓
          (hasLeast C X W s (ctx.relabel j) (rawCons d e) f ⊓
            (hasLeast C X W s (ctx.relabel j) (rawCons d e) g ⊓
              hasLeast C X W s (ctx.relabel j) d a)))) →
      D B Δ (windowAt Z (ctx.relabel j) (rawCons d e) f ⊓
        (windowAt Z (ctx.relabel j) (rawCons d e) g ⊓ windowAt Z (ctx.relabel j) d a)) →
      D B Δ (hopCalls R L (ctx.relabel j) (ty.relabel j) (before.relabel j) (cert.relabel j)
        (after.relabel j) (q.relabel j) (w.relabel j) (r.relabel j)) →
      D B Δ (goal.relabel j)) → D B Γ goal := by
  intro W Z raw L R app head notL checked bottom child
  obtain ⟨report⟩ := checked
  let calls := Derivation.conjunctionRight report
  let value := Derivation.conjunctionRight calls
  have seed := exact_OpenStrictDualAuxProfileFromStack L₀ ctx ty (auxiliaryTerm dom cod fn arg) before app
  have actual := exact_OpenStrictDualAuxProfileFromStack L₀ ctx ty q before ⟨Derivation.conjunctionLeft value⟩
  obtain ⟨shape⟩ := exact_OpenAuxiliarySourceFromSharedProfile L₀ ctx ty dom cod fn arg q w r before h
    seed actual head notL
  let args : Fin 5 → OTerm α := ![ctx,ty,q,w,r]
  obtain ⟨step⟩ := conjunctionRecover (guardedRaw raw) (targetGate i cv tv L) args
    ⟨Derivation.conjunctionLeft calls⟩
  have unwrapped := exact_OpenLiteralAtomicRawUnderlying raw args ⟨Derivation.conjunctionLeft step⟩
  let P := root (leafAtAuxiliary leaf)
  let F := fallback other
  obtain ⟨both⟩ := exact_OpenDualTypedRawEndpoints P F W Z V ctx ty q w r unwrapped
  let wins := Derivation.conjunctionRight both
  apply exact_OpenPerTickNonLambdaAuxiliary C X s leaf other rawBase rawT V ctx ty q w r goal
    ⟨Derivation.conjunctionLeft shape⟩ ⟨Derivation.conjunctionRight shape⟩ ⟨Derivation.conjunctionLeft both⟩
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
    obtain ⟨e⟩ := exact_OpenLiteralAtomicGuardedLeastSingleton (headerLeast (fullAuxiliaryDecorator L₀))
      sc st rr kk onBottom (queryAtInput rr kk atom)
    exact bottom β j Δ keep ⟨symm e⟩
  · intro _ β j Δ d e f a w' d' e' g a' keep fields projected
    have held := renameInto (⟨report⟩ : D B Γ (hopCalls R L ctx ty before cert after q w r)) j Δ keep
    rw [fieldsRename] at held
    obtain ⟨childRow⟩ := projected
    have first := renameInto (⟨Derivation.conjunctionLeft wins⟩ :
      D B Γ (windowAt Z ctx ty q)) j Δ keep
    have second := renameInto (⟨Derivation.conjunctionRight wins⟩ :
      D B Γ (windowAt Z ctx ty r)) j Δ keep
    change D B Δ ((windowGraph Z ctx ty q).relabel j) at first
    change D B Δ ((windowGraph Z ctx ty r).relabel j) at second
    rw [windowRename] at first second
    let entries := Derivation.conjunctionRight childRow
    let domains := Derivation.conjunctionRight entries
    obtain ⟨c⟩ := exact_OpenStrictDualChild C X s leaf other rawBase base rawT V T
      (ctx.relabel j) (ty.relabel j) (q.relabel j) (w.relabel j) (r.relabel j)
      d e f a w' d' e' g a' fields first second ⟨Derivation.conjunctionLeft childRow⟩
      ⟨Derivation.conjunctionLeft domains⟩
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight domains)⟩
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight domains)⟩
    exact child β j Δ d e f a w' d' e' g a' keep fields
      ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft c) entries⟩
      ⟨Derivation.conjunctionRight c⟩ held

#print axioms exact_OpenStrictDualAuxProfileFromStack
#print axioms exact_OpenStrictDualCertifiedAuxBottomOrChild
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictDualCertifiedCasesProof
