module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.TailMapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.TailHeadRangeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.SecondRangeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open Continuation20261114.HeadWindowBooleanRange
open Continuation20261114.HeadWindowBooleanRange.InductionSyntaxProof (booleanRename)
open SyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nonzeroSecond (n : Nat) (key param deps parentRank values rest out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRank n parentRank)))
    (hp : Nonempty (Derivation body Delta (graph2 rank parentRank key param)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hn : Nonempty (Derivation body Delta (eqn deps z).not))
    (hm : Nonempty (Derivation body Delta (graph2 (Equation.answerMap n) values deps param)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode rest values)))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode out rest))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  apply ListCasesProof.nonzeroCases deps _ hn
  intro beta j Theta child tail hj hc
  rw [booleanRename]
  have ihj := renameInto ih j Theta hj
  rw [belowRankRename] at ihj
  have hpj := renameInto hp j Theta hj
  have hdj := renameInto hd j Theta hj
  have hmj := renameInto hm j Theta hj
  have htj := renameInto ht j Theta hj
  have hhj := renameInto hh j Theta hj
  rw [graph2Rename] at hpj hdj hmj
  rw [graph1Rename] at htj hhj
  have htail := TailMapProof.recover n (deps.relabel j) child tail (param.relabel j) (values.relabel j) (rest.relabel j) hc hmj htj
  exact TailHeadRangeProof.headRange n (key.relabel j) (param.relabel j) (deps.relabel j) (parentRank.relabel j)
    child tail (rest.relabel j) (out.relabel j) ihj hpj hdj hc htail hhj

theorem secondRange (n : Nat) (key param deps parentRank values rest out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRank n parentRank)))
    (hp : Nonempty (Derivation body Delta (graph2 rank parentRank key param)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 (Equation.answerMap n) values deps param)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode rest values)))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode out rest))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  let A := eqn deps z
  apply formulaCases A
  · have hz : Nonempty (Derivation body (A :: Delta) (eqn deps z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hm0 := headTransport (Equation.answerMap n) values deps z (Fin.cons param Fin.elim0) hz (withHyp hm A)
    have he := valueUnique (Equation.answerMap n) values z ![z,param] hm0 (AnswersProof.nilMap n param)
    have ht0 := headTransport InternalListCodec.tailCode rest values z Fin.elim0 he (withHyp ht A)
    have hrest := valueUnique InternalListCodec.tailCode rest z (Fin.cons z Fin.elim0) ht0
      SixSol20261113.Context.ReverseForwardRowsProof.tailZero
    exact HeadRangeProof.headNil out (headTransport InternalListCodec.headCode out rest z Fin.elim0 hrest (withHyp hh A))
  · exact nonzeroSecond n key param deps parentRank values rest out (withHyp ih A.not) (withHyp hp A.not)
      (withHyp hd A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm A.not) (withHyp ht A.not) (withHyp hh A.not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.SecondRangeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.SecondRangeProof
