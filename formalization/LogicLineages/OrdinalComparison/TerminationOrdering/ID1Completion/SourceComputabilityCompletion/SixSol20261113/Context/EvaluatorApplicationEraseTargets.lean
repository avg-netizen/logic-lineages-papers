module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedApplicationErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorApplicationEraseTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationValidityClosure
open OriginalRawSyntaxTransport
/-- Literal original constructor transport under actual parent and BOTH child
packed erasures. No source, evaluator, retained-key or semantic premise. -/
def ActualApplicationErase : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (arrow d e fp ap fn arg parent parentOut fnOut argOut erasedType cutoff : OTerm alpha)
 (psi : Formula alpha),
 Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg parent)) →
 Nonempty (Derivation body Delta (graph3 erasePackedRaw parentOut erasedType cutoff parent)) →
 Nonempty (Derivation body Delta (graph3 erasePackedRaw fnOut erasedType cutoff fn)) →
 Nonempty (Derivation body Delta (graph3 erasePackedRaw argOut erasedType cutoff arg)) →
 (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
   (∀ h ∈ Delta, h.relabel j ∈ Theta) →
   ∀ fpOut apOut : OTerm beta,
   Nonempty (Derivation body Theta (applicationConstructors (arrow.relabel j) (d.relabel j)
     (e.relabel j) fpOut apOut (fnOut.relabel j) (argOut.relabel j) (parentOut.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) →
 Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorApplicationEraseTargets
