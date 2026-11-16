module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.GuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.RecognizesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRuleSuffix LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GuardProof
theorem recognizes {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (isS : Bool) (ptag ctag atag fval : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hf : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (a b c : Term ctx) (hguard : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (guards isS fval a b c)) :
 Computes p G (recognizer isS) (lineValue isS ptag ctag atag a b c ::ᵥ nil) (.succ .zero) := by
 let outLine := lineValue isS ptag ctag atag a b c
 let av := outLine ::ᵥ nil
 obtain ⟨hfirst,hsecond,hthird⟩ := DecoderProof.arguments p G isS ptag ctag atag hp hc a b c
 have hA := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hguard
 have hRest := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hguard
 have hga := guardAt p G fval hf firstArg av a hfirst hA
 cases isS with
 | false =>
  have hgb := guardAt p G fval hf secondArg av b hsecond hRest
  have hrebuilt := ConstructorProof.lineAt p G ptag ctag atag hp hc ha false firstArg secondArg (constant 1 0)
   av a b (.zero : Term ctx) hfirst hsecond (constantValue p G av 0)
  have hmatch := binary p G av equalCode (.projection 0) (line false firstArg secondArg thirdArg)
   outLine outLine (.succ .zero) (projection p G av 0) hrebuilt (equalDiagonal p G outLine)
  have hguards := choosePositive p G av _ (constant 1 0) _ .zero (.succ .zero) hga hgb
  exact choosePositive p G av _ (constant 1 0) _ .zero (.succ .zero) hmatch hguards
 | true =>
  have hB := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hRest
  have hC := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hRest
  have hgb := guardAt p G fval hf secondArg av b hsecond hB
  have hgc := guardAt p G fval hf thirdArg av c (hthird rfl) hC
  have hrebuilt := ConstructorProof.lineAt p G ptag ctag atag hp hc ha true firstArg secondArg thirdArg
   av a b c hfirst hsecond (hthird rfl)
  have hmatch := binary p G av equalCode (.projection 0) (line true firstArg secondArg thirdArg)
   outLine outLine (.succ .zero) (projection p G av 0) hrebuilt (equalDiagonal p G outLine)
  have hbc := choosePositive p G av _ (constant 1 0) _ .zero (.succ .zero) hgb hgc
  have hguards := choosePositive p G av _ (constant 1 0) _ .zero (.succ .zero) hga hbc
  exact choosePositive p G av _ (constant 1 0) _ .zero (.succ .zero) hmatch hguards
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.RecognizesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.RecognizesProof
