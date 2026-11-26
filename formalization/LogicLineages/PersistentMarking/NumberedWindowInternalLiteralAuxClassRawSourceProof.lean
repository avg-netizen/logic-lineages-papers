module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationLeastDecoratorProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxCertifiedCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassRawSourceProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalControlGraphSupportProof (headTransport valueUnique)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (termReports)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D exact_OpenAtomicLeastReport)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralHeaderLeastOpenProof (exact_OpenLiteralHeaderLeastReport)
open NumberedWindowInternalLiteralApplicationLeastDecoratorProof (auxiliaryDecorator)
open NumberedWindowInternalLiteralAuxClassLeastProof (auxClassLeast functionClass argumentClass)
open NumberedWindowInternalLiteralAuxClassLeastOpenProof (exact_OpenLiteralAuxClassLeastReport)
open NumberedWindowInternalLiteralAuxClassSharedProof (exact_OpenSharedAuxChildClasses)
open NumberedWindowInternalLiteralAuxClassReadProof (exact_OpenLiteralFunctionClass exact_OpenLiteralArgumentClass)
open NumberedWindowInternalLiteralAuxProfileLeastProof (auxProfileLeast)
open NumberedWindowInternalLiteralAuxProfileLeastOpenProof
  (exact_OpenLiteralAuxProfileFields exact_OpenLiteralAuxCoordinateTransfer)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem moveRaw (p : Program 2) (ctx q r out : OTerm α)
    (e : D B Γ (eqn q r)) (held : D B Γ (programGraph p out ![ctx,q])) :
    D B Γ (programGraph p out ![ctx,r]) := by
  unfold programGraph at held ⊢
  apply graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula p)
    out ![ctx,q] ![ctx,r] _ held
  intro i
  rw [onEquality]
  exact Fin.cases (⟨refl ctx⟩ : D B Γ (eqn ctx ctx))
    (Fin.cases e (fun n => Fin.elim0 n)) i

theorem exact_OpenAuxClassStackReport (L : Program 3) (ctx ty q k : OTerm α)
    (held : D B Γ (programGraph (guardedLeast (headerLeast (auxiliaryDecorator L))) (suc k) ![ctx,ty,q])) :
    D B Γ (programGraph (auxClassLeast (auxProfileLeast L)) (suc k) ![ctx,ty,q]) := by
  obtain ⟨one⟩ := exact_OpenAtomicLeastReport (headerLeast (auxiliaryDecorator L)) ctx ty q k held
  obtain ⟨two⟩ := exact_OpenLiteralHeaderLeastReport (auxiliaryDecorator L) ctx ty q k
    ⟨Derivation.conjunctionLeft one⟩
  exact ⟨Derivation.conjunctionLeft two⟩

/-- On a contextual raw certificate source, the two annotations and
the actual successful calls for the function and argument are those
of the preceding application seed. The raw children themselves
need not be the literal original children; the class witnesses are
transferred using the actual comparison programs. -/
theorem exact_OpenAuxRawChildMinima (L : Program 3)
    (ctx ty dom cod fn arg q d e f a k m n : OTerm α)
    (left : D B Γ (programGraph (guardedLeast (headerLeast (auxiliaryDecorator L))) (suc k)
      ![ctx,ty,auxiliaryTerm dom cod fn arg]))
    (right : D B Γ (programGraph (guardedLeast (headerLeast (auxiliaryDecorator L))) (suc k) ![ctx,ty,q]))
    (parts : D B Γ (eqn q (auxiliaryTerm d e f a)))
    (fnMin : D B Γ (programGraph (auxProfileLeast L) (suc m) ![ctx,rawCons dom cod,fn]))
    (argMin : D B Γ (programGraph (auxProfileLeast L) (suc n) ![ctx,dom,arg])) :
    D B Γ (eqn d dom) ∧ D B Γ (eqn e cod) ∧
    D B Γ (programGraph (auxProfileLeast L) (suc m) ![ctx,rawCons d e,f]) ∧
    D B Γ (programGraph (auxProfileLeast L) (suc n) ![ctx,d,a]) := by
  let seed := auxiliaryTerm dom cod fn arg
  let step := auxiliaryTerm d e f a
  let L₀ := auxProfileLeast L
  obtain ⟨qEq⟩ := parts
  obtain ⟨sourceShape,sourceFields⟩ := termReports (body := B) (Γ := Γ) dom cod fn arg
  obtain ⟨candidateShape,candidateFields⟩ := termReports (body := B) (Γ := Γ) d e f a
  have rawShape : D B Γ (unary termShape (suc z) q) :=
    headTransport termShape (suc z) step q ![] ⟨symm qEq⟩ candidateShape
  have app := exact_OpenAuxClassStackReport L ctx ty seed k left
  have direct := exact_OpenAuxClassStackReport L ctx ty q k right
  obtain ⟨padL⟩ := exact_OpenLiteralAuxClassLeastReport L₀ ctx ty seed k app
  obtain ⟨padR⟩ := exact_OpenLiteralAuxClassLeastReport L₀ ctx ty q k direct
  obtain ⟨profileL⟩ := exact_OpenLiteralAuxProfileFields L ctx ty seed k
    ⟨Derivation.conjunctionLeft padL⟩ sourceShape
  obtain ⟨profileR⟩ := exact_OpenLiteralAuxProfileFields L ctx ty q k
    ⟨Derivation.conjunctionLeft padR⟩ rawShape
  have domK := (exact_OpenLiteralAuxCoordinateTransfer (field 0) seed k dom
    ⟨Derivation.conjunctionLeft profileL⟩).1 sourceFields.1
  have codK := (exact_OpenLiteralAuxCoordinateTransfer (field 1) seed k cod
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight profileL)⟩).1 sourceFields.2.1
  have domQ := (exact_OpenLiteralAuxCoordinateTransfer (field 0) q k dom
    ⟨Derivation.conjunctionLeft profileR⟩).2 domK
  have codQ := (exact_OpenLiteralAuxCoordinateTransfer (field 1) q k cod
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight profileR)⟩).2 codK
  have rawDom : D B Γ (unary (field 0) d q) :=
    headTransport (field 0) d step q ![] ⟨symm qEq⟩ candidateFields.1
  have rawCod : D B Γ (unary (field 1) e q) :=
    headTransport (field 1) e step q ![] ⟨symm qEq⟩ candidateFields.2.1
  obtain ⟨callF,callA⟩ := exact_OpenSharedAuxChildClasses L₀ ctx ty seed q k (suc m) (suc n)
    app direct sourceShape rawShape
  have classF := callF ((exact_OpenLiteralFunctionClass L₀ ctx dom cod fn arg (suc m)).1 fnMin)
  have classA := callA ((exact_OpenLiteralArgumentClass L₀ ctx dom cod fn arg (suc n)).1 argMin)
  exact ⟨valueUnique (field 0) d dom ![q] rawDom domQ,valueUnique (field 1) e cod ![q] rawCod codQ,
    (exact_OpenLiteralFunctionClass L₀ ctx d e f a (suc m)).2 (moveRaw (functionClass L₀) ctx q step (suc m) ⟨qEq⟩ classF),
    (exact_OpenLiteralArgumentClass L₀ ctx d e f a (suc n)).2 (moveRaw (argumentClass L₀) ctx q step (suc n) ⟨qEq⟩ classA)⟩

#print axioms exact_OpenAuxClassStackReport
#print axioms exact_OpenAuxRawChildMinima
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassRawSourceProof
