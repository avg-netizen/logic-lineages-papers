module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletion
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalOriginalOrderSyntaxProof (ltF)
open InternalClosedPrograms (allBlock)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Concrete state/agenda/potential/fuel hypothesis. Result stack is retained
in the actual state pairing, never replaced by a native work projection. -/
def Entry {alpha : Type} (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B fuel input work results before output : OTerm alpha) : Formula alpha :=
 graph2 InternalPairing.pairing input work results ⊓
 (OriginalHereditaryInternalAgenda.Agenda H M W c B work ⊓
 (graph2 OriginalHereditaryAgendaPotential.agenda before work B ⊓
 (ltF before (suc fuel) ⊓ graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output fuel input)))
def Empty {alpha : Type} (output : OTerm alpha) : Formula alpha := graph1 InternalUnpair.left z output
def rowBody {alpha : Type} (R : Program 2) (H : Program 1) (M W : Program 2) (c B fuel : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
 (Entry R H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (fuel.relabel Sum.inl)
  (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))).imp (Empty (.var (.inr 4)))
def Row {alpha : Type} (R : Program 2) (H : Program 1) (M W : Program 2) (c B fuel : OTerm alpha) : Formula alpha := allBlock (rowBody R H M W c B fuel)
/-- Explicit proof-side staging supplier. It must be discharged from actual
frame admissibility, scheduler effects, and potential descent before a concrete
completion endpoint can be claimed. Not a native evaluator assumption. -/
def StepLaw (R : Program 2) (H : Program 1) (M W : Program 2) : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (c B input work results before next nextWork nextResults after : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Agenda H M W c B work)) →
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda before work B)) →
 Nonempty (Derivation body Delta (eqn work z).not) →
 Nonempty (Derivation body Delta (graph1 (OriginalHereditaryCombinedStep.step R) next input)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing next nextWork nextResults)) →
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda after nextWork B)) →
 Nonempty (Derivation body Delta
  (OriginalHereditaryInternalAgenda.Agenda H M W c B nextWork ⊓ ltF after before))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletion
