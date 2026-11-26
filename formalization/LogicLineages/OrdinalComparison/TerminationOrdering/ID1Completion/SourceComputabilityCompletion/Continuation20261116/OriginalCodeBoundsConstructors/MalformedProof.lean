module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.AnswersProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.MalformedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open Continuation20261115 OriginalCodeBoundsRecursion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem malformedValue (n : Nat) (raw : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) z raw))) :
    Nonempty (Derivation body Delta (graph1 (bounds n) z raw)) := by
  apply programCases (OriginalCodeBoundsEquation.answers n) (Fin.cons raw (Fin.cons z Fin.elim0)) _
  intro beta j Theta values hj ha
  simp only [consTermRename,emptyRename,zRelabel] at ha
  simp only [graph1Rename,zRelabel]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph1Rename,zRelabel] at hgj
  exact AnswersProof.fromLayer n (raw.relabel j) values z ha (OriginalCodeBoundsRecursion.SupportProof.zeroValue n (raw.relabel j) values z hgj)

theorem internalMalformed : Targets.InternalMalformed := by
  intro n body alpha Delta raw out hg
  have hz := malformedValue n raw hg
  constructor
  · intro ho
    exact valueUnique (bounds n) out z ![raw] ho hz
  · intro he
    obtain ⟨he⟩ := he
    exact outputTransport (bounds n) z out ![raw] ⟨symm he⟩ hz
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.MalformedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.MalformedProof
