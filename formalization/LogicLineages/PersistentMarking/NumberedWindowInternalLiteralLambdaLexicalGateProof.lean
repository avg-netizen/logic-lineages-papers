module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaTypedRawCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaLexicalGateProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn zRelabel sucRelabel)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (cellEquation)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (consOfGraph)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)

def lexicalSlot (p : Program 1) (i : Fin 5) : Program 5 :=
  .composition p (fun _ : Fin 1 => .projection i)

def lexicalBinder : Program 5 := lexicalSlot (field 0) 2
def lexicalDomain : Program 5 := lexicalSlot cellHead 1
def lexicalCodomain : Program 5 := lexicalSlot cellTail 1
def lexicalSourceBody : Program 5 := lexicalSlot (field 1) 2
def lexicalTargetBody : Program 5 := lexicalSlot (field 1) 4
def lexicalContext : Program 5 := consOf lexicalBinder (.projection 0)

def lexicalArrow : Program 5 :=
  conjunction (lexicalSlot cellGood 1) (.composition equalityTest ![lexicalDomain,lexicalBinder])

def lexicalWindowAt (W : Program 3) (p : Program 5) : Program 5 :=
  .composition W ![lexicalContext,lexicalCodomain,p]

/-- Keep the literal type spine and both body windows at the real
extended lexical context, rather than reinterpreting the parent context. -/
def lambdaLexicalGate (W : Program 3) : Program 5 :=
  conjunction lexicalArrow (conjunction (lexicalWindowAt W lexicalSourceBody) (lexicalWindowAt W lexicalTargetBody))

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem lexicalSlotAt (p : Program 1) (i : Fin 5) (out : OTerm α)
    (tape : Fin 5 → OTerm α) (h : D B Γ (unary p out (tape i))) :
    D B Γ (programGraph (lexicalSlot p i) out tape) := by
  apply compositionValue p (fun _ : Fin 1 => .projection i) out tape ![tape i] h
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue i tape

theorem exact_OpenLambdaLexicalRowsAt (W : Program 3)
    (ctx ty q w r d a b dom cod : OTerm α)
    (gate : D B Γ (programGraph (lambdaLexicalGate W) (suc z) ![ctx,ty,q,w,r]))
    (binder : D B Γ (unary (field 0) d q)) (src : D B Γ (unary (field 1) a q))
    (dst : D B Γ (unary (field 1) b r)) (domain : D B Γ (unary cellHead dom ty))
    (codomain : D B Γ (unary cellTail cod ty)) :
    D B Γ (eqn ty (rawCons d cod)) ∧ D B Γ (windowAt W (rawCons d ctx) cod a) ∧
      D B Γ (windowAt W (rawCons d ctx) cod b) := by
  let tape : Fin 5 → OTerm α := ![ctx,ty,q,w,r]
  have readD : D B Γ (programGraph lexicalBinder d tape) := lexicalSlotAt (field 0) 2 d tape binder
  have readT : D B Γ (programGraph lexicalCodomain cod tape) := lexicalSlotAt cellTail 1 cod tape codomain
  have readDom : D B Γ (programGraph lexicalDomain dom tape) := lexicalSlotAt cellHead 1 dom tape domain
  have sc : D B Γ (programGraph lexicalContext (rawCons d ctx) tape) :=
    consOfGraph lexicalBinder (.projection 0) d ctx tape readD (projectionValue 0 tape)
  obtain ⟨outer⟩ := conjunctionRecover lexicalArrow
    (conjunction (lexicalWindowAt W lexicalSourceBody) (lexicalWindowAt W lexicalTargetBody)) tape gate
  obtain ⟨type⟩ := conjunctionRecover (lexicalSlot cellGood 1) (.composition equalityTest ![lexicalDomain,lexicalBinder])
    tape ⟨Derivation.conjunctionLeft outer⟩
  have good : D B Γ (unary cellGood (suc z) ty) := by
    apply compositionRecover cellGood (fun _ : Fin 1 => .projection 1) (suc z) tape ![ty]
      ⟨Derivation.conjunctionLeft type⟩
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 tape
  have same := equalityOfAcceptance dom d
    (compositionRecover equalityTest ![lexicalDomain,lexicalBinder] (suc z) tape ![dom,d]
      ⟨Derivation.conjunctionRight type⟩ (fun i => Fin.cases readDom (Fin.cases readD (fun e => Fin.elim0 e)) i))
  have head := ID1Completion.InternalControlGraphSupportProof.outputTransport cellHead dom d ![ty] same domain
  obtain ⟨parts⟩ := conjunctionRecover (lexicalWindowAt W lexicalSourceBody)
    (lexicalWindowAt W lexicalTargetBody) tape ⟨Derivation.conjunctionRight outer⟩
  have next (p : Program 5) (x : OTerm α) (term : D B Γ (programGraph p x tape))
      (win : D B Γ (programGraph (lexicalWindowAt W p) (suc z) tape)) :
      D B Γ (windowAt W (rawCons d ctx) cod x) := by
    apply compositionRecover W ![lexicalContext,lexicalCodomain,p] (suc z) tape ![rawCons d ctx,cod,x] win
    intro i
    exact Fin.cases sc (Fin.cases readT (Fin.cases term (fun e => Fin.elim0 e))) i
  exact ⟨cellEquation ty d cod good head codomain,
    next lexicalSourceBody a (lexicalSlotAt (field 1) 2 a tape src) ⟨Derivation.conjunctionLeft parts⟩,
    next lexicalTargetBody b (lexicalSlotAt (field 1) 4 b tape dst) ⟨Derivation.conjunctionRight parts⟩⟩

#print axioms lambdaLexicalGate
#print axioms lexicalSlotAt
#print axioms exact_OpenLambdaLexicalRowsAt
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaLexicalGateProof
