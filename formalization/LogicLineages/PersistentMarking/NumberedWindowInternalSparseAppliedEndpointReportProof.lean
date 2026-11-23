module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAppliedEndpointReportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalFixedWindowVertexDispatchSupportProof (constantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeParsedEmitter (addressTag addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (reportBinder reportUnfold)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Four real graph calls at the exact original packed address. -/
theorem canonical (ctx cod k : OTerm α) :
    Nonempty (Derivation body Γ (addressReport (addressTerm ctx cod k) ctx cod k)) := by
  have v : Nonempty (Derivation body Γ (unary addressTag (numeral 3) (addressTerm ctx cod k))) := by
    unfold addressTag
    rw [exact_DispatchControlAST.2.1]
    exact constantValue 1 3 ![addressTerm ctx cod k]
  obtain ⟨⟨well⟩,⟨⟨c⟩,⟨t⟩,⟨key⟩,_⟩⟩ := packedNode addressTag (numeral 3) [ctx,cod,k] v
  exact ⟨Derivation.conjunctionIntroduction well
    (Derivation.conjunctionIntroduction c (Derivation.conjunctionIntroduction t key))⟩

private theorem move (p : Program 1) (out a b : OTerm α)
    (e : Nonempty (Derivation body Γ (eqn a b)))
    (seen : Nonempty (Derivation body Γ (unary p out a))) :
    Nonempty (Derivation body Γ (unary p out b)) := by
  have s : Nonempty (Derivation body Γ (programGraph p out (Fin.cons a Fin.elim0))) := seen
  exact headTransport p out a b Fin.elim0 e s

/-- The actual output equation identifies the report address; no numerical
raw endpoint reflection or externally guessed canonical code is used. -/
theorem fromAddressEquation (y ctx cod k : OTerm α)
    (eq : Nonempty (Derivation body Γ (eqn y (addressTerm ctx cod k)))) :
    Nonempty (Derivation body Γ (addressReport y ctx cod k)) := by
  obtain ⟨d⟩ := canonical (body := body) (Γ := Γ) ctx cod k
  obtain ⟨e⟩ := eq
  let a := addressTerm ctx cod k
  have back : Nonempty (Derivation body Γ (eqn a y)) := ⟨symm e⟩
  obtain ⟨g⟩ := move addressGood (suc z) a y back ⟨Derivation.conjunctionLeft d⟩
  have rest := Derivation.conjunctionRight d
  obtain ⟨c⟩ := move rawContext ctx a y back ⟨Derivation.conjunctionLeft rest⟩
  obtain ⟨t⟩ := move rawResult cod a y back ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight rest)⟩
  obtain ⟨k⟩ := move rawLeast k a y back ⟨Derivation.conjunctionRight (Derivation.conjunctionRight rest)⟩
  exact ⟨Derivation.conjunctionIntroduction g
    (Derivation.conjunctionIntroduction c (Derivation.conjunctionIntroduction t k))⟩

/-- Opens the actual canonical application output with every witness report
needed by the installed positive checker, and retains its exact equation. -/
theorem endpointCases (least : Program 3) (ctx cod raw y : OTerm α) (goal : Formula α)
    (out : Nonempty (Derivation body Γ (outputReport least ctx cod raw y)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (k : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (programGraph least (suc k) ![ctx.relabel j,cod.relabel j,raw.relabel j])) →
      Nonempty (Derivation body Δ (eqn (y.relabel j) (addressTerm (ctx.relabel j) (cod.relabel j) k))) →
      Nonempty (Derivation body Δ (addressReport (y.relabel j) (ctx.relabel j) (cod.relabel j) k)) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  rw [reportUnfold] at out
  obtain ⟨ex⟩ := out
  let j : α → α ⊕ Fin 1 := Sum.inl
  let row := reportBinder least ctx cod raw y
  let Δ := row :: Γ.map weaken
  let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  have keep (p : Formula α) (h : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,h,rfl⟩)
  have facts : Derivation body Δ row := Derivation.hypothesis List.mem_cons_self
  have he : Nonempty (Derivation body Δ (eqn (y.relabel j) (addressTerm (ctx.relabel j) (cod.relabel j) k))) :=
    ⟨Derivation.conjunctionRight facts⟩
  obtain ⟨done⟩ := next (α ⊕ Fin 1) j Δ k keep ⟨Derivation.conjunctionLeft facts⟩ he
    (fromAddressEquation (y.relabel j) (ctx.relabel j) (cod.relabel j) k he)
  exact ⟨Derivation.existentialElimination ex done⟩

#print axioms canonical
#print axioms fromAddressEquation
#print axioms endpointCases
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAppliedEndpointReportProof
