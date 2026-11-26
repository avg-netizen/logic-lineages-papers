module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassLeastOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassReadProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (termReports)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (consOfGraph)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalFreshProbeDispatchProgram (predOne)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)
open NumberedWindowInternalLiteralAuxClassLeastProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem pairRename {β : Type} (a b : OTerm α) (j : α → β) :
    (fun i : Fin 2 => ((![a,b] : Fin 2 → OTerm α) i).relabel j) = ![a.relabel j,b.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun n => Fin.elim0 n)) i

private theorem atRawReport (p : Program 1) (ctx q a : OTerm α)
    (graph : D B Γ (unary p a q)) : D B Γ (programGraph (atRaw p) a ![ctx,q]) := by
  apply compositionValue p (Fin.cons (.projection 1) Fin.elim0) a ![ctx,q] ![q] graph
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 1 ![ctx,q]

/-- The very same projected class call is equivalent to the packed
least on the actual arrow and raw function fields of the literal seed. -/
theorem exact_OpenLiteralFunctionClass (L : Program 3) (ctx d c f a out : OTerm α) :
    let seed := auxiliaryTerm d c f a
    (D B Γ (programGraph L out ![ctx,rawCons d c,f]) →
      D B Γ (programGraph (functionClass L) out ![ctx,seed])) ∧
    (D B Γ (programGraph (functionClass L) out ![ctx,seed]) →
      D B Γ (programGraph L out ![ctx,rawCons d c,f])) := by
  intro seed
  let tape : Fin 2 → OTerm α := ![ctx,seed]
  let fs : Fin 3 → Program 2 := Fin.cons (.projection 0)
    (Fin.cons childArrow (Fin.cons (atRaw (field 2)) Fin.elim0))
  obtain ⟨_,fields⟩ := termReports (body := B) (Γ := Γ) d c f a
  have label : D B Γ (programGraph childArrow (rawCons d c) tape) :=
    consOfGraph (atRaw (field 0)) (atRaw (field 1)) d c tape
      (atRawReport (field 0) ctx seed d fields.1)
      (atRawReport (field 1) ctx seed c fields.2.1)
  have value : D B Γ (programGraph (atRaw (field 2)) f tape) :=
    atRawReport (field 2) ctx seed f fields.2.2.1
  have inputs : ∀ i, D B Γ (programGraph (fs i) ((![ctx,rawCons d c,f] : Fin 3 → OTerm α) i) tape) :=
    fun i => Fin.cases (projectionValue 0 tape) (Fin.cases label (Fin.cases value (fun n => Fin.elim0 n))) i
  exact ⟨fun h => compositionValue L fs out tape ![ctx,rawCons d c,f] h inputs,
    fun h => compositionRecover L fs out tape ![ctx,rawCons d c,f] h inputs⟩

theorem exact_OpenLiteralArgumentClass (L : Program 3) (ctx d c f a out : OTerm α) :
    let seed := auxiliaryTerm d c f a
    (D B Γ (programGraph L out ![ctx,d,a]) →
      D B Γ (programGraph (argumentClass L) out ![ctx,seed])) ∧
    (D B Γ (programGraph (argumentClass L) out ![ctx,seed]) →
      D B Γ (programGraph L out ![ctx,d,a])) := by
  intro seed
  let tape : Fin 2 → OTerm α := ![ctx,seed]
  let fs : Fin 3 → Program 2 := Fin.cons (.projection 0)
    (Fin.cons (atRaw (field 0)) (Fin.cons (atRaw (field 3)) Fin.elim0))
  obtain ⟨_,fields⟩ := termReports (body := B) (Γ := Γ) d c f a
  have label : D B Γ (programGraph (atRaw (field 0)) d tape) :=
    atRawReport (field 0) ctx seed d fields.1
  have value : D B Γ (programGraph (atRaw (field 3)) a tape) :=
    atRawReport (field 3) ctx seed a fields.2.2.2.1
  have inputs : ∀ i, D B Γ (programGraph (fs i) ((![ctx,d,a] : Fin 3 → OTerm α) i) tape) :=
    fun i => Fin.cases (projectionValue 0 tape) (Fin.cases label (Fin.cases value (fun n => Fin.elim0 n))) i
  exact ⟨fun h => compositionValue L fs out tape ![ctx,d,a] h inputs,
    fun h => compositionRecover L fs out tape ![ctx,d,a] h inputs⟩

private theorem rightRaw (ctx q t : OTerm α) :
    D B Γ (programGraph resultRaw t ![ctx,q,suc t]) := by
  let xs : Fin 3 → OTerm α := ![ctx,q,suc t]
  unfold resultRaw
  rw [exact_DispatchControlAST.2.2.1]
  apply compositionValue ID1Completion.InternalEqualityTest.predecessor
    (Fin.cons (.projection 2) Fin.elim0) t xs ![suc t] (predecessorSuccessor t)
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 2 xs

theorem exact_OpenChildClassEquality (p : Program 2) (ctx q t a b : OTerm α)
    (left : D B Γ (programGraph p a ![ctx,q]))
    (right : D B Γ (programGraph p b ![ctx,t]))
    (compared : D B Γ (programGraph (compareChildClass p) (suc z) ![ctx,q,suc t])) :
    D B Γ (eqn a b) := by
  let xs : Fin 3 → OTerm α := ![ctx,q,suc t]
  have first : D B Γ (programGraph (onSource p) a xs) := by
    apply compositionValue p (Fin.cons (.projection 0) (Fin.cons (.projection 1) Fin.elim0)) a xs ![ctx,q] left
    exact fun i => Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs) (fun e => Fin.elim0 e)) i
  have second : D B Γ (programGraph (onResult p) b xs) := by
    apply compositionValue p (Fin.cons (.projection 0) (Fin.cons resultRaw Fin.elim0)) b xs ![ctx,t] right
    exact fun i => Fin.cases (projectionValue 0 xs) (Fin.cases (rightRaw ctx q t) (fun e => Fin.elim0 e)) i
  unfold compareChildClass at compared
  rw [exact_DispatchControlAST.2.2.2.1] at compared
  have exactCompare := compositionRecover equalityTest
    (Fin.cons (onSource p) (Fin.cons (onResult p) Fin.elim0)) (suc z) xs (Fin.cons a (Fin.cons b Fin.elim0))
    compared (fun i => Fin.cases first (Fin.cases second (fun e => Fin.elim0 e)) i)
  exact equalityOfAcceptance a b exactCompare

/-- Both directions transfer the exact encoded child least output
through the physical comparison, even on open terms. -/
theorem exact_OpenChildClassTransfer (p : Program 2) (ctx q t a : OTerm α)
    (compared : D B Γ (programGraph (compareChildClass p) (suc z) ![ctx,q,suc t])) :
    (D B Γ (programGraph p a ![ctx,q]) → D B Γ (programGraph p a ![ctx,t])) ∧
    (D B Γ (programGraph p a ![ctx,t]) → D B Γ (programGraph p a ![ctx,q])) := by
  constructor
  · intro left
    apply programCases p ![ctx,t] _
    intro β j Δ v keep other
    rw [programRename,pairRename]
    rw [pairRename] at other
    have one := renameInto left j Δ keep
    simp only [programRename,pairRename] at one
    have checks := renameInto compared j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at checks
    obtain ⟨e⟩ := exact_OpenChildClassEquality p (ctx.relabel j) (q.relabel j) (t.relabel j)
      (a.relabel j) v one other checks
    exact outputTransport p v (a.relabel j) ![ctx.relabel j,t.relabel j] ⟨symm e⟩ other
  · intro right
    apply programCases p ![ctx,q] _
    intro β j Δ v keep other
    rw [programRename,pairRename]
    rw [pairRename] at other
    have one := renameInto right j Δ keep
    simp only [programRename,pairRename] at one
    have checks := renameInto compared j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at checks
    have e := exact_OpenChildClassEquality p (ctx.relabel j) (q.relabel j) (t.relabel j)
      v (a.relabel j) other one checks
    exact outputTransport p v (a.relabel j) ![ctx.relabel j,q.relabel j] e other

#print axioms exact_OpenLiteralFunctionClass
#print axioms exact_OpenLiteralArgumentClass
#print axioms exact_OpenChildClassEquality
#print axioms exact_OpenChildClassTransfer
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassReadProof
