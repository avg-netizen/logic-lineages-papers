module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.GuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.RecognizesKProof
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
 (a b c : Term ctx) (hguard : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (guards false fval a b c)) :
 Computes p G (recognizer false) (lineValue false ptag ctag atag a b c ::ᵥ nil) (.succ .zero) := by
 let outLine : Term ctx := lineValue false ptag ctag atag a b c
 let av : List.Vector (Term ctx) 1 := outLine ::ᵥ nil
 obtain ⟨hfirst,hsecond,hthird⟩ := DecoderProof.arguments p G false ptag ctag atag hp hc a b c
 have hA : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (formulaValid fval a) :=
  Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hguard
 have hga : Computes p G (formulaGuard firstArg) av (.succ .zero) := guardAt p G fval hf firstArg av a hfirst hA
 have hB : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (formulaValid fval b) :=
  Hilbert.Local.mp (.base (.logical (.andRight _ _))) hguard
 have hgb : Computes p G (formulaGuard secondArg) av (.succ .zero) := guardAt p G fval hf secondArg av b hsecond hB
 have hrebuilt0 : Computes p G (line false firstArg secondArg (constant 1 0)) av
  (lineValue false ptag ctag atag a b .zero) :=
  ConstructorProof.lineAt p G ptag ctag atag hp hc ha false firstArg secondArg (constant 1 0)
   av a b (.zero : Term ctx) hfirst hsecond (constantValue p G av 0)
 have hprogram : line false firstArg secondArg (constant 1 0) = line false firstArg secondArg thirdArg := by
  simp only [line,conclusion,arguments,Bool.false_eq_true,if_false]
 have hvalue : lineValue false ptag ctag atag a b .zero = outLine := by
  simp only [outLine,lineValue,conclusionValue,argumentsValue,Bool.false_eq_true,if_false]
 have hrebuilt : Computes p G (line false firstArg secondArg thirdArg) av outLine := by
  rw [hprogram,hvalue] at hrebuilt0
  exact hrebuilt0
 have hmatch : Computes p G (applyTwo equalCode (.projection 0) (line false firstArg secondArg thirdArg)) av (.succ .zero) :=
  binary p G av equalCode (.projection 0) (line false firstArg secondArg thirdArg)
   outLine outLine (.succ .zero) (projection p G av 0) hrebuilt (equalDiagonal p G outLine)
 have hguards : Computes p G (conjunction (formulaGuard firstArg) (formulaGuard secondArg)) av (.succ .zero) :=
  choosePositive p G av (formulaGuard firstArg) (constant 1 0) (formulaGuard secondArg) .zero (.succ .zero) hga hgb
 exact choosePositive p G av (applyTwo equalCode (.projection 0) (line false firstArg secondArg thirdArg))
  (constant 1 0) (conjunction (formulaGuard firstArg) (formulaGuard secondArg)) .zero (.succ .zero) hmatch hguards
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.RecognizesKProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.RecognizesKProof
