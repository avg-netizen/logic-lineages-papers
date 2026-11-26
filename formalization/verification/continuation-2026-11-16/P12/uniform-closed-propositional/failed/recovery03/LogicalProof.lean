module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.DecoderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.LogicalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRuleSuffix LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem guardAt {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (fval : Nat)
 (hf : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (q : Program arity) (av : List.Vector (Term ctx) arity) (a : Term ctx)
 (hq : Computes p G q av a) (hvalid : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (formulaValid fval a)) :
 Computes p G (formulaGuard q) av (.succ .zero) := by
 have hv : Computes p G LiteralSyntaxValidator.formulaValidator ((.zero : Term ctx) ::ᵥ a ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag fval 2
   LiteralSyntaxValidator.formulaValidator ht hf ctx (.zero ::ᵥ a ::ᵥ nil)
  exact ⟨localTrans _ _ _ (.base hcopy) hvalid⟩
 exact binary p G av LiteralSyntaxValidator.formulaValidator (constant arity 0) q
  .zero a (.succ .zero) (constantValue p G av 0) hq hv
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
theorem rawAcceptanceImp {n ctx : Nat} (p : Program n) (old : Program 1)
 (isS : Bool) (ltag ptag ctag atag fval : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,logicalLeaf old⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hf : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (a b c : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (guards isS fval a b c)
   (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall ltag (lineValue isS ptag ctag atag a b c)) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let A := guards isS fval a b c
 let G := [A]
 let av := lineValue isS ptag ctag atag a b c ::ᵥ nil
 have hguard : Hilbert.Local T ctx G A := .hypothesis List.mem_cons_self
 have hrec := recognizes p G isS ptag ctag atag fval hp hc ha hf a b c hguard
 have hout : Computes p G (logicalLeaf old) av (.succ .zero) := by
  cases isS with
  | false =>
   have hk := choosePositive p G av (recognizer false) old (constant 1 1) .zero (.succ .zero)
    hrec (constantValue p G av 1)
   exact RawCumulativeArithmetic.ArithmeticProof.chooseBoth p G
    (recognizer true) (choose (recognizer false) old (constant 1 1)) (constant 1 1) av (.succ .zero)
    hk (constantValue p G av 1)
  | true =>
   exact choosePositive p G av (recognizer true) (choose (recognizer false) old (constant 1 1))
    (constant 1 1) .zero (.succ .zero) hrec (constantValue p G av 1)
 obtain ⟨hout⟩ := hout ltag hl
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
theorem exactInternalLogical : Targets.InternalLogical := by
 intro n p old isS qtag ltag ptag ctag atag fval hq hl hp hc ha hf ctx a b c
 obtain ⟨hline⟩ := ConstructorProof.exactInternalLine n p isS qtag ptag ctag atag hq hp hc ha ctx a b c
 obtain ⟨haccept⟩ := rawAcceptanceImp p old isS ltag ptag ctag atag fval hl hp hc ha hf a b c
 have hleaf := HistoryLookup.DestructorProof.unaryCallCongruence ltag _ _ hline
 let T := GorbowPRNumeralCalculation.Theory p
 let A := guards isS fval a b c
 have hA : Hilbert.Local T ctx [A] A := .hypothesis List.mem_cons_self
 have hresult := Hilbert.Local.mp (.base haccept) hA
 have hout := localTrans _ _ _ (.base hleaf) hresult
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.LogicalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.LogicalProof
