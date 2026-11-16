module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.ListCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.FirstRangeProof
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

theorem nonzeroHead (n : Nat) (key param deps parentRank values out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRank n parentRank)))
    (hp : Nonempty (Derivation body Delta (graph2 rank parentRank key param)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hn : Nonempty (Derivation body Delta (eqn deps z).not))
    (hm : Nonempty (Derivation body Delta (graph2 (Equation.answerMap n) values deps param)))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode out values))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  apply ListCasesProof.nonzeroCases deps _ hn
  intro beta j Theta child tail hj hc
  rw [booleanRename]
  have ihj := renameInto ih j Theta hj
  rw [belowRankRename] at ihj
  have hpj := renameInto hp j Theta hj
  have hdj := renameInto hd j Theta hj
  have hmj := renameInto hm j Theta hj
  have hhj := renameInto hh j Theta hj
  rw [graph2Rename] at hpj hdj hmj
  rw [graph1Rename] at hhj
  exact HeadRangeProof.consHeadIn n (key.relabel j) (param.relabel j) (deps.relabel j) (parentRank.relabel j)
    (deps.relabel j) child tail (values.relabel j) (out.relabel j) ihj hpj hdj
    (ListCasesProof.memberHead (deps.relabel j) child tail hc) hc hmj hhj

theorem headRange (n : Nat) (key param deps parentRank values out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRank n parentRank)))
    (hp : Nonempty (Derivation body Delta (graph2 rank parentRank key param)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 (Equation.answerMap n) values deps param)))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode out values))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  let A := eqn deps z
  apply formulaCases A
  · have hz : Nonempty (Derivation body (A :: Delta) (eqn deps z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hm0 := headTransport (Equation.answerMap n) values deps z (Fin.cons param Fin.elim0) hz (withHyp hm A)
    exact HeadRangeProof.nilMapHead n param values out hm0 (withHyp hh A)
  · exact nonzeroHead n key param deps parentRank values out (withHyp ih A.not) (withHyp hp A.not)
      (withHyp hd A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm A.not) (withHyp hh A.not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.FirstRangeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.FirstRangeProof
