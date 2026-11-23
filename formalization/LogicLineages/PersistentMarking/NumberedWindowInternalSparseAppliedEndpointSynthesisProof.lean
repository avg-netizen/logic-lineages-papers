module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAppliedEndpointReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBackwardProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAppliedEndpointSynthesisProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn emb)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (reportBinder reportUnfold reportInstance)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs applicationReport)
open NumberedWindowInternalSparseApplicationFrontendOpenBindingProof (supply)
open NumberedWindowInternalSparseApplicationFrontendOpenBackwardProof (backward)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A successful exact least call gives an original, not invented, application
output witness with its own precise lexical context and codomain. -/
theorem outputFromLeast (least : Program 3) (ctx cod raw k : OTerm α)
    (call : Nonempty (Derivation body Γ (programGraph least (suc k) ![ctx,cod,raw]))) :
    Nonempty (Derivation body Γ (outputReport least ctx cod raw (addressTerm ctx cod k))) := by
  let y := addressTerm ctx cod k
  rw [reportUnfold]
  obtain ⟨l⟩ := call
  have equation : Derivation body Γ (eqn y (addressTerm ctx cod k)) := refl y
  have payload := Derivation.conjunctionIntroduction l equation
  exact ⟨Derivation.existentialIntroduction (phi := reportBinder least ctx cod raw y)
    (emb k) ((reportInstance least ctx cod raw y k).symm ▸ payload)⟩

/-- The actual guarded canonical application is built on exactly the same
function and argument, using their real raw parser row and the successful
least evaluator on the selected auxiliary raw term. The real codomain is
kept in both canonical output address and output report. -/
theorem acceptedFromLeast (i : Program 1) (least : Program 3)
    (f u ctx result dom cod fn arg k : OTerm α)
    (hf : Nonempty (Derivation body Γ (unary i (suc z) f)))
    (hu : Nonempty (Derivation body Γ (unary i (suc z) u)))
    (parsed : Nonempty (Derivation body Γ (parsedApplicationInputs f u ctx result dom cod fn arg)))
    (call : Nonempty (Derivation body Γ
      (programGraph least (suc k) ![ctx,cod,auxiliaryTerm dom cod fn arg]))) :
    Nonempty (Derivation body Γ (programGraph (applicationGuard i least) (suc z)
      ![f,u,addressTerm ctx cod k])) := by
  let y := addressTerm ctx cod k
  obtain ⟨p⟩ := parsed
  obtain ⟨o⟩ := outputFromLeast least ctx cod (auxiliaryTerm dom cod fn arg) k call
  have row := supply least f u y ctx result dom cod fn arg ⟨Derivation.conjunctionIntroduction p o⟩
  obtain ⟨fOK⟩ := hf
  obtain ⟨uOK⟩ := hu
  obtain ⟨v⟩ := row
  have same : Nonempty (Derivation body Γ (applicationReport i least f u y)) :=
    ⟨Derivation.conjunctionIntroduction fOK (Derivation.conjunctionIntroduction uOK v)⟩
  exact backward i least f u y same

#print axioms outputFromLeast
#print axioms acceptedFromLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAppliedEndpointSynthesisProof
