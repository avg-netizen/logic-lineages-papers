module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.GuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.RecognizesExistential
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
 (hguard : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (guards true fval a b)) :
 Computes p G (recognizer true) (lineValue true ptag ctag atag a b ::ᵥ nil) (.succ .zero) := by
 let outLine := lineValue true ptag ctag atag a b
 let av := outLine ::ᵥ nil
 obtain ⟨hfirst,_⟩ := DecoderProof.arguments p G true ptag ctag atag hp hc a b
 have hga := GuardProof.guardAt p G 1 fval hf firstArg av a hfirst hguard
 have hrebuilt0 := OriginalQuantifierLogicalProducers.LineGraph.lineAt p G ptag ctag atag hp hc ha true
  firstArg (constant 1 0) av a (.zero : Term ctx) hfirst (constantValue p G av 0)
 have hprogram : line true firstArg (constant 1 0) = line true firstArg secondArg := by
  simp only [line,conclusion,arguments,if_true]
 have hvalue : lineValue true ptag ctag atag a .zero = outLine := by
  simp only [outLine,lineValue,conclusionValue,argumentsValue,if_true]
 have hrebuilt : Computes p G (line true firstArg secondArg) av outLine := by
  rw [hprogram,hvalue] at hrebuilt0
  exact hrebuilt0
 have hmatch := binary p G av equalCode (.projection 0) (line true firstArg secondArg)
  outLine outLine (.succ .zero) (projection p G av 0) hrebuilt (equalDiagonal p G outLine)
 exact choosePositive p G av (applyTwo equalCode (.projection 0) (line true firstArg secondArg))
  (constant 1 0) (formulaGuard 1 firstArg) .zero (.succ .zero) hmatch hga

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.RecognizesExistential
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalExtension.RecognizesExistential
