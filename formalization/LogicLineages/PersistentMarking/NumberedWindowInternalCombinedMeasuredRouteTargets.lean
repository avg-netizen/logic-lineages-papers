module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredRoundTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredRouteTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (Programs)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalMeasuredAuxExchangeTargets (measuredExchange)
open NumberedWindowInternalSparseDirectedRounds (rounds roundsTape)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedTargets (MeasurePreservingEdge)

/-- This extends the old V/R/W source package at the exact point where
its clients must choose an exchange. The original formation and
cover are not overridden. Downstream edge, rounds and least are
computed accessors of this one installed exchange. -/
structure InstalledRoute where
  source : Programs
  settings : Settings
  base : Program 2

abbrev install (s : Settings) (V TV M M0 : Program 1) (B : Program 2) (T : Program 1)
    (base : Program 2) : InstalledRoute :=
  ⟨combinedPrograms s V TV M M0 B T,s,base⟩

abbrev InstalledRoute.cover (K : InstalledRoute) : Program 3 := K.source.cover
abbrev InstalledRoute.window (K : InstalledRoute) : Program 3 :=
  thinMatchingWindow K.cover K.settings K.source.W K.source.V
abbrev InstalledRoute.measure (K : InstalledRoute) : Program 1 := selectedMeasure K.source.R
abbrev InstalledRoute.directed (K : InstalledRoute) : Program 2 := directedX K.base K.source.V
abbrev InstalledRoute.plain (K : InstalledRoute) : Program 2 :=
  guardedExchange K.cover K.settings (thinPairedExchange K.directed)
abbrev InstalledRoute.exchange (K : InstalledRoute) : Program 2 :=
  guardedExchange K.cover K.settings (thinPairedExchange (measuredExchange K.measure K.directed))
abbrev InstalledRoute.edge (K : InstalledRoute) : Program 4 := edge4 K.exchange K.window
abbrev InstalledRoute.round (K : InstalledRoute) : Program 5 := rounds K.edge
abbrev InstalledRoute.least (K : InstalledRoute) : Program 3 :=
  packedLeastProgram K.cover K.exchange K.window K.settings

def InstalledRoute.RoundAt (K : InstalledRoute) {α : Type}
    (out fuel vertices ctx ty seed : OTerm α) : Formula α :=
  programGraph K.round out (roundsTape fuel vertices ctx ty seed)

def InstalledRoute.LeastAt (K : InstalledRoute) {α : Type}
    (ctx ty seed value : OTerm α) : Formula α :=
  programGraph K.least (suc value) ![ctx,ty,seed]

def ExactInstalledMeasuredEdge : Prop :=
  ∀ (s : Settings) (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2),
    let K := install s V TV M M0 B T base
    MeasurePreservingEdge K.edge K.measure ∧
    (∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty a b : OTerm α),
      Nonempty (Derivation body Γ (acceptEdge K.edge ctx ty a b)) →
      Nonempty (Derivation body Γ (acceptEdge (edge4 K.plain K.window) ctx ty a b)))

/-- Convert only the same original paired edge on the same tape, under
actual identical selected measure reports. No equality of rounds or
least results across different exchanges is asserted. -/
def ExactInstalledAdmissionFromSharedMeasure : Prop :=
  ∀ (s : Settings) (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty a b p : OTerm α),
    let K := install s V TV M M0 B T base
    Nonempty (Derivation body Γ (acceptEdge (edge4 K.plain K.window) ctx ty a b)) →
    Nonempty (Derivation body Γ (unary K.measure p a)) →
    Nonempty (Derivation body Γ (unary K.measure p b)) →
    Nonempty (Derivation body Γ (acceptEdge K.edge ctx ty a b))

def ExactInstalledMeasuredRound : Prop :=
  ∀ (s : Settings) (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod f arg μ m fuel vertices out k : OTerm α),
    let K := install s V TV M M0 B T base
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt K.window ctx dom arg)) →
    Nonempty (Derivation body Γ (unary K.measure μ f)) →
    Nonempty (Derivation body Γ (K.LeastAt ctx cod (auxiliaryTerm dom cod f arg) m)) →
    Nonempty (Derivation body Γ (K.RoundAt out fuel vertices ctx (rawCons dom cod) f)) →
    Nonempty (Derivation body Γ (memberGraph out k)) →
    Nonempty (Derivation body Γ (unary K.measure μ k ⊓ K.LeastAt ctx cod (auxiliaryTerm dom cod k arg) m))

def FullInstalledMeasuredRoute : Prop :=
  ExactInstalledMeasuredEdge ∧ ExactInstalledAdmissionFromSharedMeasure ∧ ExactInstalledMeasuredRound

end LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredRouteTargets
