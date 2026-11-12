module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalIndexedPrefixCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionRawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupCallbacksProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel eqn)
open InternalFiniteBlocksSubstitutionProof (renameIdentity)
open InternalSliceInductionSyntaxProof (eqnRename)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalInternalRawExpansionLookupTargets
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem firstRename (psi : Formula alpha) (raw parameter index child : OTerm alpha)
 (h : First body Delta psi raw parameter index child)
 {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
 (hin : ∀ f ∈ Delta, f.relabel j ∈ Theta) :
 First body Theta (psi.relabel j) (raw.relabel j) (parameter.relabel j) (index.relabel j) (child.relabel j) := by
 intro gamma k Xi arity ha hk hA he hj
 have inc : ∀ f ∈ Delta, f.relabel (k ∘ j) ∈ Xi := by
   intro f hf
   simpa only [← formulaRelabelComposition] using hk _ (hin f hf)
 have hh := h gamma (k ∘ j) Xi arity ha inc
   (by simpa only [Term.relabel_relabel] using hA)
   (by simpa only [Term.relabel_relabel] using he)
   (by simpa only [Term.relabel_relabel] using hj)
 simpa only [formulaRelabelComposition] using hh

theorem secondRename (psi : Formula alpha) (raw parameter index child : OTerm alpha)
 (h : Second body Delta psi raw parameter index child)
 {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
 (hin : ∀ f ∈ Delta, f.relabel j ∈ Theta) :
 Second body Theta (psi.relabel j) (raw.relabel j) (parameter.relabel j) (index.relabel j) (child.relabel j) := by
 intro gamma k Xi hk hA he hj
 have inc : ∀ f ∈ Delta, f.relabel (k ∘ j) ∈ Xi := by
   intro f hf
   simpa only [← formulaRelabelComposition] using hk _ (hin f hf)
 have hh := h gamma (k ∘ j) Xi  inc
   (by simpa only [Term.relabel_relabel] using hA)
   (by simpa only [Term.relabel_relabel] using he)
   (by simpa only [Term.relabel_relabel] using hj)
 simpa only [formulaRelabelComposition] using hh

theorem deletedRename (psi : Formula alpha) (raw parameter index child : OTerm alpha)
 (h : Deleted body Delta psi raw parameter index child)
 {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
 (hin : ∀ f ∈ Delta, f.relabel j ∈ Theta) :
 Deleted body Theta (psi.relabel j) (raw.relabel j) (parameter.relabel j) (index.relabel j) (child.relabel j) := by
 intro gamma k Xi arity row cutoff count ha hk hA he hd hl hb hv
 have inc : ∀ f ∈ Delta, f.relabel (k ∘ j) ∈ Xi := by
   intro f hf
   simpa only [← formulaRelabelComposition] using hk _ (hin f hf)
 have hh := h gamma (k ∘ j) Xi arity row cutoff count ha inc
   (by simpa only [Term.relabel_relabel] using hA)
   (by simpa only [Term.relabel_relabel] using he)
   (by simpa only [Term.relabel_relabel] using hd)
   (by simpa only [Term.relabel_relabel] using hl)
   (by simpa only [Term.relabel_relabel] using hb)
   (by simpa only [Term.relabel_relabel] using hv)
 simpa only [formulaRelabelComposition] using hh

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupCallbacksProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupCallbacksProof
