module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity.ConstructorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity.LogicalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix TwoSol20261113.ReflexivityRecognizer
open SixSol20261112.Fuel NamedArithmeticGraph
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
theorem decoded {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (args : List.Vector (Term ctx) arity) (q : Program arity) (side : Bool) (a b : Term ctx)
 (h : Computes p G q args (HistoryKernel.pairCall ptag a b)) :
 Computes p G (applyOne (HistoryDecoder.decoder side) q) args
  (HistoryDecoder.StepNormalProof.chosen side a b) :=
 unary p G args (HistoryDecoder.decoder side) q _ _ h (decoder p G ptag hp side a b)

theorem rawAcceptanceImp {n ctx : Nat} (p : Program n) (old : Program 1)
 (ltag ptag ctag atag vtag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,logicalLeaf old⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,termValidator⟩)
 (raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (leafCall vtag raw) (.succ .zero))
   (.equal (leafCall ltag (RawReflexivity.lineValue ptag ctag atag raw)) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let V := Formula.equal (leafCall vtag raw) (.succ .zero)
 let G := [V]
 let eq := HistoryLookup.consCall ctag (.zero : Term ctx) (HistoryAppend.appendCall atag raw raw)
 let line := LiteralReflexivityQuote.lineValue ptag ctag eq raw
 let args := line ::ᵥ nil
 let refs := HistoryKernel.pairCall ptag (.zero : Term ctx) .zero
 let single := HistoryLookup.consCall ctag raw .zero
 let pairArgs := HistoryKernel.pairCall ptag single refs
 let payload := HistoryKernel.pairCall ptag (Term.numeral 11) pairArgs
 let rule := HistoryKernel.pairCall ptag .zero payload
 let conclusion := HistoryKernel.pairCall ptag eq rule
 have hline : Computes p G (.projection 0) args (HistoryKernel.pairCall ptag .zero conclusion) :=
  projection p G args 0
 have hconclusion := decoded p G ptag hp args (.projection 0) true .zero conclusion hline
 have hrule := decoded p G ptag hp args (right (.projection 0)) true eq rule hconclusion
 have hpayload := decoded p G ptag hp args (right (right (.projection 0))) true .zero payload hrule
 have hpairArgs := decoded p G ptag hp args (right (right (right (.projection 0)))) true
  (Term.numeral 11) pairArgs hpayload
 have hsingle : Computes p G argsCode args single :=
  decoded p G ptag hp args (right (right (right (right (.projection 0))))) false single refs hpairArgs
 have hhead : Computes p G HistoryLookup.head (single ::ᵥ nil) raw := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalHeadCons n p tag ctag ht hc ctx raw .zero
  exact ⟨.base h⟩
 have hraw : Computes p G termCode args raw := unary p G args HistoryLookup.head argsCode _ _ hsingle hhead
 have hz := constantValue p G args 0
 have hone := constantValue p G args 1
 have h11 := constantValue p G args 11
 have hcopyPair (a b : Term ctx) := copies p G HistoryCodec.pair ptag hp (a ::ᵥ b ::ᵥ nil)
 have hcopyCons (a b : Term ctx) := copies p G HistoryCodec.cons ctag hc (a ::ᵥ b ::ᵥ nil)
 have hcopyAppend := copies p G HistoryAppend.append atag ha (raw ::ᵥ raw ::ᵥ nil)
 have hdup := binary p G args HistoryAppend.append termCode termCode raw raw _ hraw hraw hcopyAppend
 have heq : Computes p G (reflexiveRaw termCode) args eq :=
  binary p G args HistoryCodec.cons (constant 1 0) _ .zero _ eq hz hdup (hcopyCons _ _)
 have hsingle' := binary p G args HistoryCodec.cons termCode (constant 1 0) raw .zero single hraw hz (hcopyCons _ _)
 have hrefs := binary p G args HistoryCodec.pair (constant 1 0) (constant 1 0) .zero .zero refs hz hz (hcopyPair _ _)
 have hpa := binary p G args HistoryCodec.pair _ _ single refs pairArgs hsingle' hrefs (hcopyPair _ _)
 have hpay := binary p G args HistoryCodec.pair _ _ (Term.numeral 11) pairArgs payload h11 hpa (hcopyPair _ _)
 have hr := binary p G args HistoryCodec.pair _ _ .zero payload rule hz hpay (hcopyPair _ _)
 have hco := binary p G args HistoryCodec.pair _ _ eq rule conclusion heq hr (hcopyPair _ _)
 have hrebuilt : Computes p G (reflexiveLine termCode) args line :=
  binary p G args HistoryCodec.pair _ _ .zero conclusion line hz hco (hcopyPair _ _)
 have hmatch := binary p G args equalCode (.projection 0) (reflexiveLine termCode)
  line line (.succ .zero) (projection p G args 0) hrebuilt (equalDiagonal p G line)
 have hvalid' : Computes p G termValidator (raw ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag vtag 1 termValidator ht hv ctx (raw ::ᵥ nil)
  have h : Hilbert.Local T ctx G V := .hypothesis List.mem_cons_self
  exact ⟨HistoryCodec.ArithmeticSupport.localTrans _ _ _ (.base hcopy) h⟩
 have hterm := unary p G args termValidator termCode raw (.succ .zero) hraw hvalid'
 have hrecognizer : Computes p G recognizer args (.succ .zero) :=
  choosePositive p G args _ _ _ .zero (.succ .zero) hmatch hterm
 obtain ⟨hout⟩ := choosePositive p G args recognizer old (constant 1 1) .zero (.succ .zero)
  hrecognizer hone ltag hl
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩

theorem internalLogical : Targets.InternalLogical := by
 intro n p old qtag ltag ptag ctag atag vtag hq hl hp hc ha hv ctx raw
 obtain ⟨hline⟩ := ConstructorProof.internalLine n p qtag ptag ctag atag hq hp hc ha ctx raw
 obtain ⟨haccept⟩ := rawAcceptanceImp p old ltag ptag ctag atag vtag hl hp hc ha hv raw
 have hleaf := HistoryLookup.DestructorProof.unaryCallCongruence ltag _ _ hline
 exact ⟨Hilbert.compose (Logic.oneTransport _ _ (Support.equalitySymmetry _ _ hleaf)) haccept⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity.LogicalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity.LogicalProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity.LogicalProof.rawAcceptanceImp
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivity.LogicalProof.internalLogical
