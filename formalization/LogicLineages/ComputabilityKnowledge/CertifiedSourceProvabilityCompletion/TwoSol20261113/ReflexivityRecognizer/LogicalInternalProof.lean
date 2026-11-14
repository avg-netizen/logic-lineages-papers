module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer.TermInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer.LogicalInternalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem decoded {n arity ctx : Nat} (p : Program n) (ptag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (args : List.Vector (Term ctx) arity) (q : Program arity) (side : Bool) (a b : Term ctx)
 (h : Computes p [] q args (HistoryKernel.pairCall ptag a b)) :
 Computes p [] (applyOne (HistoryDecoder.decoder side) q) args
  (HistoryDecoder.StepNormalProof.chosen side a b) :=
 unary p [] args (HistoryDecoder.decoder side) q _ _ h (decoder p [] ptag hp side a b)

theorem rawAcceptance {n ctx : Nat} (p : Program n) (old : Program 1)
 (ltag ptag ctag atag vtag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,logicalLeaf old⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hv : (nodes p)[vtag]? = some ⟨1,termValidator⟩)
 (raw : Term ctx)
 (hvalid : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (leafCall vtag raw) (.succ .zero)))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (leafCall ltag (LiteralReflexivityQuote.lineValue ptag ctag
   (HistoryLookup.consCall ctag .zero (HistoryAppend.appendCall atag raw raw)) raw)) (.succ .zero))) := by
 let eq := HistoryLookup.consCall ctag (.zero : Term ctx) (HistoryAppend.appendCall atag raw raw)
 let line := LiteralReflexivityQuote.lineValue ptag ctag eq raw
 let args := line ::ᵥ nil
 let refs := HistoryKernel.pairCall ptag (.zero : Term ctx) .zero
 let single := HistoryLookup.consCall ctag raw .zero
 let pairArgs := HistoryKernel.pairCall ptag single refs
 let payload := HistoryKernel.pairCall ptag (Term.numeral 11) pairArgs
 let rule := HistoryKernel.pairCall ptag .zero payload
 let conclusion := HistoryKernel.pairCall ptag eq rule
 have hline : Computes p [] (.projection 0) args (HistoryKernel.pairCall ptag .zero conclusion) :=
  projection p [] args 0
 have hconclusion := decoded p ptag hp args (.projection 0) true .zero conclusion hline
 have hrule := decoded p ptag hp args (right (.projection 0)) true eq rule hconclusion
 have hpayload := decoded p ptag hp args (right (right (.projection 0))) true .zero payload hrule
 have hpairArgs := decoded p ptag hp args (right (right (right (.projection 0)))) true
  (Term.numeral 11) pairArgs hpayload
 have hsingle : Computes p [] argsCode args single :=
  decoded p ptag hp args (right (right (right (right (.projection 0))))) false single refs hpairArgs
 have hhead : Computes p [] HistoryLookup.head (single ::ᵥ nil) raw := by
  intro tag ht
  obtain ⟨h⟩ := HistoryLookup.DestructorProof.internalHeadCons n p tag ctag ht hc ctx raw .zero
  exact ⟨.base h⟩
 have hraw : Computes p [] termCode args raw := unary p [] args HistoryLookup.head argsCode _ _ hsingle hhead
 have hz := constantValue p [] args 0
 have hone := constantValue p [] args 1
 have h11 := constantValue p [] args 11
 have hcopyPair (a b : Term ctx) := copies p [] HistoryCodec.pair ptag hp (a ::ᵥ b ::ᵥ nil)
 have hcopyCons (a b : Term ctx) := copies p [] HistoryCodec.cons ctag hc (a ::ᵥ b ::ᵥ nil)
 have hcopyAppend := copies p [] HistoryAppend.append atag ha (raw ::ᵥ raw ::ᵥ nil)
 have hdup := binary p [] args HistoryAppend.append termCode termCode raw raw _ hraw hraw hcopyAppend
 have heq : Computes p [] (reflexiveRaw termCode) args eq :=
  binary p [] args HistoryCodec.cons (constant 1 0) _ .zero _ eq hz hdup (hcopyCons _ _)
 have hsingle' := binary p [] args HistoryCodec.cons termCode (constant 1 0) raw .zero single hraw hz (hcopyCons _ _)
 have hrefs := binary p [] args HistoryCodec.pair (constant 1 0) (constant 1 0) .zero .zero refs hz hz (hcopyPair _ _)
 have hpa := binary p [] args HistoryCodec.pair _ _ single refs pairArgs hsingle' hrefs (hcopyPair _ _)
 have hpay := binary p [] args HistoryCodec.pair _ _ (Term.numeral 11) pairArgs payload h11 hpa (hcopyPair _ _)
 have hr := binary p [] args HistoryCodec.pair _ _ .zero payload rule hz hpay (hcopyPair _ _)
 have hco := binary p [] args HistoryCodec.pair _ _ eq rule conclusion heq hr (hcopyPair _ _)
 have hrebuilt : Computes p [] (reflexiveLine termCode) args line :=
  binary p [] args HistoryCodec.pair _ _ .zero conclusion line hz hco (hcopyPair _ _)
 have hmatch := binary p [] args equalCode (.projection 0) (reflexiveLine termCode)
  line line (.succ .zero) (projection p [] args 0) hrebuilt (equalDiagonal p [] line)
 have hvalid' : Computes p [] termValidator (raw ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag vtag 1 termValidator ht hv ctx (raw ::ᵥ nil)
  obtain ⟨h⟩ := hvalid
  exact ⟨.base (Logic.trans _ _ _ hcopy h)⟩
 have hterm := unary p [] args termValidator termCode raw (.succ .zero) hraw hvalid'
 have hrecognizer : Computes p [] recognizer args (.succ .zero) :=
  choosePositive p [] args _ _ _ .zero (.succ .zero) hmatch hterm
 obtain ⟨hout⟩ := choosePositive p [] args recognizer old (constant 1 1) .zero (.succ .zero)
  hrecognizer hone ltag hl
 exact ⟨Hilbert.Local.finish hout⟩

theorem internalLogical : Targets.InternalLogical := by
 intro k t old n p ltag qtag etag ttag ptag ctag atag vtag hl hq he ht hp hc ha hv ctx values
 let raw := LiteralTemplateQuote.quoteCall ttag values
 let eq := HistoryLookup.consCall ctag (.zero : Term ctx) (HistoryAppend.appendCall atag raw raw)
 let line := LiteralReflexivityQuote.lineValue ptag ctag eq raw
 have htcomp : LiteralRawMP.ConstructorSupportProof.Computes p (LiteralTemplateQuote.templateQuote t) values raw := by
  intro tag htag
  exact GorbowPRInternalCoherence.Proof.registryCoherence n p tag ttag k (LiteralTemplateQuote.templateQuote t) htag ht ctx values
 have hz := LiteralRawMP.ConstructorSupportProof.constantValue p values 0
 have h11 := LiteralRawMP.ConstructorSupportProof.constantValue p values 11
 have happ := LiteralRawMP.ConstructorSupportProof.binary p values HistoryAppend.append atag ha _ _ _ _ htcomp htcomp
 have heq : LiteralRawMP.ConstructorSupportProof.Computes p (LiteralEqualityQuote.equalityQuote t t) values eq :=
  LiteralRawMP.ConstructorSupportProof.binary p values HistoryCodec.cons ctag hc _ _ _ _ hz happ
 have hs := LiteralRawMP.ConstructorSupportProof.binary p values HistoryCodec.cons ctag hc _ _ _ _ htcomp hz
 have hrefs := LiteralRawMP.ConstructorSupportProof.binary p values HistoryCodec.pair ptag hp _ _ _ _ hz hz
 have hargs := LiteralRawMP.ConstructorSupportProof.binary p values HistoryCodec.pair ptag hp _ _ _ _ hs hrefs
 have hpay := LiteralRawMP.ConstructorSupportProof.binary p values HistoryCodec.pair ptag hp _ _ _ _ h11 hargs
 have hrule := LiteralRawMP.ConstructorSupportProof.binary p values HistoryCodec.pair ptag hp _ _ _ _ hz hpay
 have hconclusion := LiteralRawMP.ConstructorSupportProof.binary p values HistoryCodec.pair ptag hp _ _ _ _ heq hrule
 obtain ⟨hquote⟩ := LiteralRawMP.ConstructorSupportProof.binary p values HistoryCodec.pair ptag hp _ _ _ _ hz hconclusion qtag hq
 have hvalid := TermInternalProof.internalTerm k t n p ttag vtag ptag ctag atag ht hv hp hc ha ctx values
 obtain ⟨haccept⟩ := rawAcceptance p old ltag ptag ctag atag vtag hl hp hc ha hv raw hvalid
 exact ⟨Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence ltag _ _ hquote) haccept⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer.LogicalInternalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityRecognizer.LogicalInternalProof
