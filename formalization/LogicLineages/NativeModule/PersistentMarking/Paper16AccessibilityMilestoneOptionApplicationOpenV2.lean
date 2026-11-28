module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneOptionApplicationV2
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBindingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreCallProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectEmitterProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneOptionApplicationOpenV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue programRename outputTransport successorValue)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalAtomicApplicationShape (addressEmitter)
open NumberedWindowInternalAtomicApplicationShapeObjectEmitterProof (addressGraph)
open NumberedWindowInternalFreshProbeDispatchWitnessSyntaxProof (binaryRename)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawDomain rawCodomain rawLeast)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm addressReports arrowReports)
open NumberedWindowInternalFreshProbeSyntaxProof (unaryRename)
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseApplicationFrontendOpenBindingProof (rowCases)
open NumberedWindowInternalSparseApplicationFrontendOpenChecks (exact_OpenGuardedApplication)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparseApplicationOutputCore (selectedLeast selectedClass outputAddress)
open NumberedWindowInternalSparseApplicationOutputCoreCallProof (selectGraph)
open NumberedWindowInternalSparseApplicationOutputCoreEmitterProof (objectTape)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
  (reportUnfold reportBinder auxiliaryRename)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open Paper16AccessibilityMilestoneOptionApplicationV2 (atInput candidateAddress optionApplicationOf)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem inputValue (p : Program 1) (slot : Fin 2) (xs : Fin 2 → OTerm α) (out : OTerm α)
    (value : Nonempty (Derivation body Γ (programGraph p out ![xs slot]))) :
    Nonempty (Derivation body Γ (programGraph (atInput p slot) out xs)) := by
  unfold atInput
  apply compositionValue p (fun _ => .projection slot) out xs ![xs slot] value
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue slot xs

private theorem emittedAddress (least : Program 3) (ctx dom cod fn arg k : OTerm α)
    (picked : Nonempty (Derivation body Γ
      (programGraph least (suc k) ![ctx, cod, auxiliaryTerm dom cod fn arg]))) :
    Nonempty (Derivation body Γ (programGraph (outputAddress least) (addressTerm ctx cod k)
      (objectTape ctx dom cod fn arg z))) := by
  let xs := objectTape ctx dom cod fn arg z
  have selected := selectGraph least (suc k) ctx dom cod fn arg z picked
  have decoded : Nonempty (Derivation body Γ (programGraph (selectedClass least) k xs)) := by
    unfold selectedClass
    apply compositionValue predecessor (fun _ => selectedLeast least) k xs ![suc k]
      (predecessorSuccessor k)
    intro i
    obtain rfl := Fin.eq_zero i
    exact selected
  unfold outputAddress
  apply compositionValue addressEmitter (![.projection 0, .projection 2, selectedClass least])
    (addressTerm ctx cod k) xs ![ctx, cod, k] (addressGraph ctx cod k)
  intro i
  exact Fin.cases (projectionValue 0 xs)
    (Fin.cases (projectionValue 2 xs) (Fin.cases decoded (fun j => Fin.elim0 j))) i

private theorem candidateFromReports (least : Program 3) (f u y ctx result dom cod fn arg : OTerm α)
    (parsed : Nonempty (Derivation body Γ (parsedApplicationInputs f u ctx result dom cod fn arg)))
    (output : Nonempty (Derivation body Γ (outputReport least ctx cod (auxiliaryTerm dom cod fn arg) y))) :
    Nonempty (Derivation body Γ (programGraph (candidateAddress least) y ![f, u])) := by
  rw [reportUnfold] at output
  obtain ⟨opened⟩ := output
  obtain ⟨fields⟩ := parsed
  let pair := Derivation.conjunctionRight
    (Derivation.conjunctionRight (Derivation.conjunctionRight fields))
  have source : Derivation body Γ (addressReports f ctx result fn) := Derivation.conjunctionLeft pair
  have argument : Derivation body Γ (addressReports u ctx dom arg) :=
    Derivation.conjunctionLeft (Derivation.conjunctionRight pair)
  have arrow : Derivation body Γ (arrowReports f dom cod) :=
    Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight pair))
  let R := reportBinder least ctx cod (auxiliaryTerm dom cod fn arg) y
  let Δ := R :: Γ.map weaken
  let j : α → α ⊕ Fin 1 := Sum.inl
  let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let c := ctx.relabel j
  let d := dom.relabel j
  let t := cod.relabel j
  let f' := f.relabel j
  let u' := u.relabel j
  let fn' := fn.relabel j
  let arg' := arg.relabel j
  let y' := y.relabel j
  let xs : Fin 2 → OTerm (α ⊕ Fin 1) := ![f', u']
  have lift (p : Program 1) (out q : OTerm α)
      (h : Nonempty (Derivation body Γ (programGraph p out ![q]))) :
      Nonempty (Derivation body Δ (programGraph p (out.relabel j) ![q.relabel j])) := by
    have moved := renameInto h j Δ (fun ψ hψ =>
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ψ, hψ, rfl⟩))
    rw [programRename, unaryRename] at moved
    exact moved
  have contextReport := lift rawContext ctx f ⟨Derivation.conjunctionLeft source⟩
  have domainReport := lift rawDomain dom f ⟨Derivation.conjunctionLeft arrow⟩
  have codomainReport := lift rawCodomain cod f ⟨Derivation.conjunctionRight arrow⟩
  have fnReport := lift rawLeast fn f ⟨Derivation.conjunctionRight (Derivation.conjunctionRight source)⟩
  have argReport := lift rawLeast arg u ⟨Derivation.conjunctionRight (Derivation.conjunctionRight argument)⟩
  have row : Derivation body Δ R := Derivation.hypothesis List.mem_cons_self
  have picked : Nonempty (Derivation body Δ
      (programGraph least (suc k) ![c, t, (auxiliaryTerm dom cod fn arg).relabel j])) :=
    ⟨Derivation.conjunctionLeft row⟩
  rw [auxiliaryRename] at picked
  have emitted := emittedAddress least c d t fn' arg' k picked
  have candidate : Nonempty (Derivation body Δ
      (programGraph (candidateAddress least) (addressTerm c t k) xs)) := by
    unfold candidateAddress
    apply compositionValue (outputAddress least) _ (addressTerm c t k) xs
      (objectTape c d t fn' arg' z) emitted
    intro i
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_
      (fun c => Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => ?_) d) c) b) a) i
    · exact inputValue rawContext 0 xs c contextReport
    · exact inputValue rawDomain 0 xs d domainReport
    · exact inputValue rawCodomain 0 xs t codomainReport
    · exact inputValue rawLeast 0 xs fn' fnReport
    · exact inputValue rawLeast 1 xs arg' argReport
    · obtain rfl := Fin.eq_zero e
      exact constantZeroValue xs
  obtain ⟨aligned⟩ := outputTransport (candidateAddress least) (addressTerm c t k) y' xs
    ⟨symm (Derivation.conjunctionRight row)⟩ candidate
  have inner : Derivation body Δ (weaken (programGraph (candidateAddress least) y ![f, u])) := by
    change Derivation body Δ ((programGraph (candidateAddress least) y ![f, u]).relabel j)
    rw [programRename, binaryRename]
    exact aligned
  exact ⟨Derivation.existentialElimination opened inner⟩

/-- Every accepted original application supplies that very result to the
concrete binary option program, inside the same open derivation. -/
theorem exact_OptionApplicationOfAccepted (i : Program 1) (least : Program 3) (f u y : OTerm α)
    (accepted : Nonempty (Derivation body Γ (programGraph (applicationGuard i least) (suc z) ![f, u, y]))) :
    Nonempty (Derivation body Γ (programGraph (optionApplicationOf i least) (suc y) ![f, u])) := by
  obtain ⟨rule⟩ := exact_OpenGuardedApplication body i least α Γ f u y
  obtain ⟨proof⟩ := accepted
  have row := Derivation.conjunctionRight (Derivation.implicationElimination
    (Derivation.conjunctionLeft rule) proof)
  have actual : Nonempty (Derivation body Γ (programGraph (candidateAddress least) y ![f, u])) := by
    apply rowCases least f u y _ ⟨Derivation.conjunctionRight row⟩
    intro β j Δ ctx result dom cod fn arg _ reported
    rw [programRename, binaryRename]
    obtain ⟨fields⟩ := reported
    exact candidateFromReports least (f.relabel j) (u.relabel j) (y.relabel j) ctx result dom cod fn arg
      ⟨Derivation.conjunctionLeft fields⟩ ⟨Derivation.conjunctionRight fields⟩
  let candidate := candidateAddress least
  let slots : Fin 3 → Program 2 := ![.projection 0, .projection 1, candidate]
  let check := Program.composition (applicationGuard i least) slots
  let positive : Program 2 := .composition .succ (fun _ : Fin 1 => candidate)
  have guard : Nonempty (Derivation body Γ (programGraph check (suc z) ![f, u])) := by
    apply compositionValue (applicationGuard i least) slots (suc z) ![f, u] ![f, u, y] ⟨proof⟩
    intro a
    exact Fin.cases (projectionValue 0 ![f, u])
      (Fin.cases (projectionValue 1 ![f, u]) (Fin.cases actual (fun b => Fin.elim0 b))) a
  have output : Nonempty (Derivation body Γ (programGraph positive (suc y) ![f, u])) := by
    apply compositionValue .succ _ (suc y) ![f, u] ![y] (successorValue ![y])
    intro a
    obtain rfl := Fin.eq_zero a
    exact actual
  exact successorBranchIntro check (constantZero 2) positive (suc y) z ![f, u] guard output

#print axioms exact_OptionApplicationOfAccepted

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneOptionApplicationOpenV2
