module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.GuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.RecognizesSProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRuleSuffix LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GuardProof
theorem recognizes {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (ptag ctag atag fval : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hf : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (a b c : Term ctx) (hguard : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (guards true fval a b c)) :
 Computes p G (recognizer true) (lineValue true ptag ctag atag a b c ::ᵥ nil) (.succ .zero) := by
 let outLine : Term ctx := lineValue true ptag ctag atag a b c
 let av : List.Vector (Term ctx) 1 := outLine ::ᵥ nil
 obtain ⟨hfirst,hsecond,hthird⟩ := DecoderProof.arguments p G true ptag ctag atag hp hc a b c
 have hA : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (formulaValid fval a) :=
  Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hguard
 have hga : Computes p G (formulaGuard firstArg) av (.succ .zero) := guardAt p G fval hf firstArg av a hfirst hA
 have hRest : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
   (.conj (formulaValid fval b) (formulaValid fval c)) :=
  Hilbert.Local.mp (.base (.logical (.andRight _ _))) hguard
 have hB : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (formulaValid fval b) :=
  Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hRest
 have hC : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (formulaValid fval c) :=
  Hilbert.Local.mp (.base (.logical (.andRight _ _))) hRest
 have hgb : Computes p G (formulaGuard secondArg) av (.succ .zero) := guardAt p G fval hf secondArg av b hsecond hB
 have hgc : Computes p G (formulaGuard thirdArg) av (.succ .zero) := guardAt p G fval hf thirdArg av c (hthird rfl) hC
 have hrebuilt : Computes p G (line true firstArg secondArg thirdArg) av outLine :=
  ConstructorProof.lineAt p G ptag ctag atag hp hc ha true firstArg secondArg thirdArg av a b c hfirst hsecond (hthird rfl)
 have hmatch : Computes p G (applyTwo equalCode (.projection 0) (line true firstArg secondArg thirdArg)) av (.succ .zero) :=
  binary p G av equalCode (.projection 0) (line true firstArg secondArg thirdArg)
   outLine outLine (.succ .zero) (projection p G av 0) hrebuilt (equalDiagonal p G outLine)
 have hbc : Computes p G (conjunction (formulaGuard secondArg) (formulaGuard thirdArg)) av (.succ .zero) :=
  choosePositive p G av (formulaGuard secondArg) (constant 1 0) (formulaGuard thirdArg) .zero (.succ .zero) hgb hgc
 have hguards : Computes p G (conjunction (formulaGuard firstArg) (conjunction (formulaGuard secondArg) (formulaGuard thirdArg))) av (.succ .zero) :=
  choosePositive p G av (formulaGuard firstArg) (constant 1 0) (conjunction (formulaGuard secondArg) (formulaGuard thirdArg)) .zero (.succ .zero) hga hbc
 exact choosePositive p G av (applyTwo equalCode (.projection 0) (line true firstArg secondArg thirdArg))
  (constant 1 0) (conjunction (formulaGuard firstArg) (conjunction (formulaGuard secondArg) (formulaGuard thirdArg))) .zero (.succ .zero) hmatch hguards
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.RecognizesSProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.RecognizesSProof
