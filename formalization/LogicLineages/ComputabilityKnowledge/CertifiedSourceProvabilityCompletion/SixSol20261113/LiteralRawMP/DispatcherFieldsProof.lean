module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherPrimitivesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherFieldsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open HistoryRuleSuffix HistoryDispatcher DispatcherSupportProof DispatcherCombinatorsProof DispatcherPrimitivesProof

theorem decoded {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag : Nat)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (args : List.Vector (Term ctx) 4)
    (q : Program 4) (right : Bool) (a b : Term ctx)
    (h : Computes p G q args (HistoryKernel.pairCall ptag a b)) :
    Computes p G (applyOne (HistoryDecoder.decoder right) q) args (HistoryDecoder.StepNormalProof.chosen right a b) :=
  unary p G args (HistoryDecoder.decoder right) q _ _ h (decoder p G ptag hp right a b)

theorem fields {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag : Nat)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (context raw ref1 index fuel history : Term ctx) :
    let args := index ::ᵥ fuel ::ᵥ history ::ᵥ lineValue ptag context raw ref1 ::ᵥ nil
    Computes p G contextCode args context ∧ Computes p G rawCode args raw ∧
    Computes p G ruleCode args (.succ (.succ .zero)) ∧
    Computes p G payloadTag args .zero ∧ Computes p G payloadArgs args .zero ∧
    Computes p G HistoryDispatcher.ref1 args ref1 ∧ Computes p G ref2 args .zero := by
  let R := HistoryKernel.pairCall ptag ref1 .zero
  let A := HistoryKernel.pairCall ptag .zero R
  let P := HistoryKernel.pairCall ptag .zero A
  let S := HistoryKernel.pairCall ptag (.succ (.succ .zero)) P
  let F := HistoryKernel.pairCall ptag raw S
  let args := index ::ᵥ fuel ::ᵥ history ::ᵥ lineValue ptag context raw ref1 ::ᵥ nil
  have hline : Computes p G lineCode args (HistoryKernel.pairCall ptag context F) := projection p G args 3
  have hcontext := decoded p G ptag hp args lineCode false context F hline
  have hF := decoded p G ptag hp args lineCode true context F hline
  have hraw := decoded p G ptag hp args (right lineCode) false raw S hF
  have hS := decoded p G ptag hp args (right lineCode) true raw S hF
  have hrule := decoded p G ptag hp args (right (right lineCode)) false (.succ (.succ .zero)) P hS
  have hP := decoded p G ptag hp args (right (right lineCode)) true (.succ (.succ .zero)) P hS
  have htag := decoded p G ptag hp args payloadCode false .zero A hP
  have hA := decoded p G ptag hp args payloadCode true .zero A hP
  have hargs := decoded p G ptag hp args (right payloadCode) false .zero R hA
  have hR := decoded p G ptag hp args (right payloadCode) true .zero R hA
  have href1 := decoded p G ptag hp args (right (right payloadCode)) false ref1 .zero hR
  have href2 := decoded p G ptag hp args (right (right payloadCode)) true ref1 .zero hR
  exact ⟨hcontext,hraw,hrule,htag,hargs,href1,href2⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherFieldsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherFieldsProof
