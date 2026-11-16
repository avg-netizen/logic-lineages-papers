module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.AnswersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.CollectProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atAnswers (n : Nat) (raw values maximum : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (ha : Nonempty (Derivation body Delta (graph2 (Equation.answers n) values raw z)))
    (hc : Nonempty (Derivation body Delta (graph1 collect maximum values))) :
    Nonempty (Derivation body Delta (graph1 (depth n) (suc maximum) raw)) :=
  AnswersProof.fromLayer n raw values (suc maximum) ha (LayerProof.positiveValue n raw values z maximum hg hc)

theorem leaf (n : Nat) (raw : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency z raw z))) :
    Nonempty (Derivation body Delta (graph1 (depth n) (suc z) raw)) :=
  atAnswers n raw z z hg (AnswersProof.answersAt n raw z z z hd (AnswersProof.nilMap n z)) CollectProof.nilValue

theorem malformedValue (n : Nat) (raw : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) z raw))) :
    Nonempty (Derivation body Delta (graph1 (depth n) z raw)) := by
  apply programCases (Equation.answers n) (Fin.cons raw (Fin.cons z Fin.elim0)) _
  intro beta j Theta values hj ha
  simp only [consTermRename,emptyRename,zRelabel] at ha
  simp only [graph1Rename,zRelabel]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  simp only [graph1Rename,zRelabel] at hgj
  exact AnswersProof.fromLayer n (raw.relabel j) values z ha (LayerProof.zeroValue n (raw.relabel j) values z hgj)

theorem internalMalformed : Targets.InternalMalformed := by
  intro n body alpha Delta raw out hg
  have hz := malformedValue n raw hg
  constructor
  · intro ho
    exact valueUnique (depth n) out z ![raw] ho hz
  · intro he
    obtain ⟨he⟩ := he
    exact outputTransport (depth n) z out ![raw] ⟨symm he⟩ hz
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ValueProof
