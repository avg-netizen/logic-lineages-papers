module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.GuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.RecognizesClassical
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open OriginalQuantifierLogicalProducers
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem recognizes {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (ptag ctag atag fval : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hf : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (a b : Term ctx)
 (hguard : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (guards false fval a b)) :
 Computes p G (recognizer false) (lineValue false ptag ctag atag a b ::ᵥ nil) (.succ .zero) := by
 let outLine := lineValue false ptag ctag atag a b
 let av := outLine ::ᵥ nil
 obtain ⟨hfirst,hsecond⟩ := DecoderProof.arguments p G false ptag ctag atag hp hc a b
 have hA : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (formulaValid 0 fval a) :=
  .mp (.base (.logical (.andLeft _ _))) hguard
 have hB : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (formulaValid 0 fval b) :=
  .mp (.base (.logical (.andRight _ _))) hguard
 have hga := GuardProof.guardAt p G 0 fval hf firstArg av a hfirst hA
 have hgb := GuardProof.guardAt p G 0 fval hf secondArg av b (hsecond rfl) hB
 have hrebuilt := OriginalQuantifierLogicalProducers.LineGraph.lineAt p G ptag ctag atag hp hc ha false
  firstArg secondArg av a b hfirst (hsecond rfl)
 have hmatch := binary p G av equalCode (.projection 0) (line false firstArg secondArg)
  outLine outLine (.succ .zero) (projection p G av 0) hrebuilt (equalDiagonal p G outLine)
 have hguards := choosePositive p G av (formulaGuard 0 firstArg) (constant 1 0) (formulaGuard 0 secondArg)
  .zero (.succ .zero) hga hgb
 exact choosePositive p G av (applyTwo equalCode (.projection 0) (line false firstArg secondArg))
  (constant 1 0) (conjunction (formulaGuard 0 firstArg) (formulaGuard 0 secondArg)) .zero (.succ .zero) hmatch hguards

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.RecognizesClassical
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.RecognizesClassical
