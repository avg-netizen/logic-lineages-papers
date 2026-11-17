module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MergeInterchangeQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MergeInterchangeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.BoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)

theorem interchange (a b c bc ac left right : OTerm alpha)
    (hbc : Nonempty (Derivation body Delta (graph2 merge bc b c)))
    (hac : Nonempty (Derivation body Delta (graph2 merge ac a c)))
    (hl : Nonempty (Derivation body Delta (graph2 merge left a bc)))
    (hr : Nonempty (Derivation body Delta (graph2 merge right b ac))) :
    Nonempty (Derivation body Delta (eqn left right)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases MergeInterchangeQueriesProof.queries ![a,b,c] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![a,b,c] i).relabel j) = ![a.relabel j,b.relabel j,c.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  obtain ⟨ha,hb,hc,hmbc,hmac,hml,hmr⟩ := MergeInterchangeQueriesProof.recover
    (a.relabel j) (b.relabel j) (c.relabel j) ys hq
  rw [eqnRelabel]
  have hbcj := renameInto hbc j Theta hj
  have hacj := renameInto hac j Theta hj
  have hlj := renameInto hl j Theta hj
  have hrj := renameInto hr j Theta hj
  rw [graph2Rename] at hbcj hacj hlj hrj
  exact MergeInterchangeAtProof.atComponents (a.relabel j) (b.relabel j) (c.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5)
    (bc.relabel j) (ac.relabel j) (left.relabel j) (right.relabel j)
    (ys 6) (ys 7) (ys 8) (ys 9) ha hb hc hbcj hacj hlj hrj hmbc hmac hml hmr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MergeInterchangeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.MergeInterchangeProof
