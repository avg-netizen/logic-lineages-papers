module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredRouteTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredClosedArgumentReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredClosedArgumentAssemblyProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredClosedArgumentProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCombinedMeasuredRouteTargets (InstalledRoute)
open NumberedWindowInternalCoverMeasuredClosedArgumentReportsProof (exact_ClosedArgumentDirectedParentReport)
open NumberedWindowInternalCoverMeasuredClosedArgumentAssemblyProof (exact_OpenPairedMeasuredEdgeFromReports)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowExchangeAlgorithm (bits)
open NumberedWindowSyntaxAlgorithm (syntaxBits)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Closed raw operands, arbitrary symbolic packed context. Only the
numeric directed parent tests are evaluated; all side reports are real
object derivations at the same exact installation. -/
theorem exact_ClosedArgumentInstalledMeasuredEdge (K : InstalledRoute)
    (fit : ActualTermExchange K.settings K.base) (syntaxFit : TermSyntaxCalibrated K.source.V)
    (dom cod fn a b : Nat)
    (argAB : (bits K.settings.equivalentHeads a b).1 = true)
    (argBA : (bits K.settings.equivalentHeads b a).1 = true)
    (left : (syntaxBits (auxRaw dom cod fn a)).1 = true)
    (right : (syntaxBits (auxRaw dom cod fn b)).1 = true)
    (ctx m cover : OTerm α) :
    let p : OTerm α := numeral (auxRaw dom cod fn a)
    let q : OTerm α := numeral (auxRaw dom cod fn b)
    let ty : OTerm α := numeral cod
    Nonempty (Derivation body Γ (windowAt K.window ctx ty p)) →
    Nonempty (Derivation body Γ (windowAt K.window ctx ty q)) →
    Nonempty (Derivation body Γ (unary K.measure m p)) →
    Nonempty (Derivation body Γ (unary K.measure m q)) →
    Nonempty (Derivation body Γ (unary (coverOption K.cover K.settings) (suc cover) p)) →
    Nonempty (Derivation body Γ (unary (coverOption K.cover K.settings) (suc cover) q)) →
    Nonempty (Derivation body Γ (acceptEdge K.edge ctx ty p q)) := by
  intro p q ty wl wr ml mr cl cr
  have forward := exact_ClosedArgumentDirectedParentReport (body := body) (Γ := Γ)
    K.settings K.base K.source.V fit syntaxFit dom cod fn a b argAB left right
  have backward := exact_ClosedArgumentDirectedParentReport (body := body) (Γ := Γ)
    K.settings K.base K.source.V fit syntaxFit dom cod fn b a argBA right left
  exact exact_OpenPairedMeasuredEdgeFromReports K.cover K.window K.settings K.directed K.measure
    ctx ty p q m cover wl wr ml mr cl cr forward backward

#print axioms exact_ClosedArgumentInstalledMeasuredEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredClosedArgumentProof
