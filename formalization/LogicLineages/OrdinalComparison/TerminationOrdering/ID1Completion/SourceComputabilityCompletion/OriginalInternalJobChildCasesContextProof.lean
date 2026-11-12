module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildCasesTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildCasesContextProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalInternalJobAdmissible OriginalInternalJobAdmissibleTransportSyntaxProof
open OriginalInternalJobChildPacket OriginalInternalJobChildCasesTargets
open OriginalRawSyntaxTransportInternalParserSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem consumerRename {beta : Type} (H : Program 1) (M W : Program 2)
 (index role typ raw cell parameter c gamma : OTerm alpha) (psi : Formula alpha)
 (next : Consumer body Delta H M W index role typ raw cell parameter c gamma psi)
 (j : alpha → beta) (Theta : List (Formula beta)) (hj : ∀ p ∈ Delta, p.relabel j ∈ Theta) :
 Consumer body Theta H M W (index.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j)
  (cell.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (psi.relabel j) := by
 intro epsilon k Xi outRole outType outRaw outGamma outParam annotation hk hp
 have hi : ∀ p ∈ Delta, p.relabel (k ∘ j) ∈ Xi := by
  intro p h
  simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hk (p.relabel j) (hj p h)
 have hp' := hp
 simp only [Term.relabel_relabel] at hp'
 simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using
  next epsilon (k ∘ j) Xi outRole outType outRaw outGamma outParam annotation hi hp'

theorem consumerWeaken (H : Program 1) (M W : Program 2)
 (index role typ raw cell parameter c gamma : OTerm alpha) (psi : Formula alpha)
 (next : Consumer body Delta H M W index role typ raw cell parameter c gamma psi)
 (Theta : List (Formula alpha)) (hj : ∀ p ∈ Delta, p ∈ Theta) :
 Consumer body Theta H M W index role typ raw cell parameter c gamma psi := by
 intro beta j Xi outRole outType outRaw outGamma outParam annotation hk hp
 exact next beta j Xi outRole outType outRaw outGamma outParam annotation
  (fun p h => hk p (hj p h)) hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildCasesContextProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildCasesContextProof
