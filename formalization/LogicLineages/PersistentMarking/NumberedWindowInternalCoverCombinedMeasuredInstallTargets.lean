module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedMeasuredInstallDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedMeasuredInstallTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseApplicationFrontendTargets (applicationReport)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedTargets (MeasurePreservingEdge)
open NumberedWindowInternalCoverCombinedMeasuredInstall (install)

/-- A successful actual scalar call at the reported original address supplies
the physical window and the same measured packed least fixed point. In
particular, a function-window premise need not be inferred from an arbitrary
successful least call. -/
def ExactInstalledCarrierCoordinates : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (s : Settings) (cv tv : Program 1) (root other : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (q ctx ty k : OTerm α),
    let Q := install s V TV M M0 B T base cv tv root other
    Nonempty (Derivation body Γ (addressReport q ctx ty k)) →
    Nonempty (Derivation body Γ (unary Q.scalar (suc z) q)) →
    Nonempty (Derivation body Γ (unary cv (suc z) ctx ⊓
      (unary tv (suc z) ty ⊓ (windowAt Q.window ctx ty k ⊓
        leastGraph Q.source.cover Q.exchange Q.window s ctx ty k k))))

/-- Conversely, the original report and the same physical checks reconstruct
unit acceptance by the installed scalar. This closes the wrapper equivalence,
not just a one-way weakening of its admission predicate. -/
def ExactInstalledCarrierFromCoordinates : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (s : Settings) (cv tv : Program 1) (root other : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (q ctx ty k : OTerm α),
    let Q := install s V TV M M0 B T base cv tv root other
    Nonempty (Derivation body Γ (addressReport q ctx ty k)) →
    Nonempty (Derivation body Γ (unary cv (suc z) ctx ⊓
      (unary tv (suc z) ty ⊓ (windowAt Q.window ctx ty k ⊓
        leastGraph Q.source.cover Q.exchange Q.window s ctx ty k k)))) →
    Nonempty (Derivation body Γ (unary Q.scalar (suc z) q))

/-- Both directions of the unchanged original application report, now at the
one installed scalar and measured least. No carrier or output-success premise
is added to the original report. -/
def ExactInstalledApplicationReport : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (s : Settings) (cv tv : Program 1) (root other : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (f u y : OTerm α),
    let Q := install s V TV M M0 B T base cv tv root other
    let accepted := programGraph Q.application (suc z) ![f,u,y]
    let reported := applicationReport Q.scalar Q.least f u y
    Nonempty (Derivation body Γ ((accepted.imp reported) ⊓ (reported.imp accepted)))

/-- The actual installed member-edge program preserves the selected source
measure. No preservation assumption is imposed on the unrestricted directed
exchange; the installed program includes its literal comparison guard. -/
def ExactInstalledMeasurePreserving : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (s : Settings) (cv tv : Program 1) (root other : Program 3),
    let Q := install s V TV M M0 B T base cv tv root other
    MeasurePreservingEdge Q.edge (selectedMeasure Q.source.R)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedMeasuredInstallTargets
