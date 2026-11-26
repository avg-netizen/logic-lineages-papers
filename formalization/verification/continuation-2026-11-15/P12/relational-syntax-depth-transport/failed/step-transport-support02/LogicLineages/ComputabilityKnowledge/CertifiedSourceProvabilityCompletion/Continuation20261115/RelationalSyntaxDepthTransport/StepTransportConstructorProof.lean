module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportWitnessProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportTaskProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportConstructorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open ConstructorStepTargets
/-- All18 original constructor arms, with arbitrary raw heads. Actual old success
identifies the old output; task relation supplies both new kind and bound. -/
theorem constructorTransport {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (stag etag ptag ctag atag len q l r : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (oh ot nh nt tok result : Term ctx) (ctor : Constructor)
 (hh : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (taskRelation l r oh nh))
 (htail : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (stackRelation len q l r ot nt))
 (hk : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (call l (oh ::ᵥ nil)) (Term.numeral (kind ctor))))
 (htok : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal tok (Term.numeral (token ctor))))
 (hold : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.stepCall stag (.succ (HistoryLookup.consCall ctag oh ot)) tok) (.succ result))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (StepTransportTargets.witnesses stag len q l r (HistoryLookup.consCall ctag nh nt) tok result)) := by
 let ob := call r (oh ::ᵥ nil)
 let nb := call r (nh ::ᵥ nil)
 have hkind := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 have hbound := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hh
 have hnewkind := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hkind) hk
 obtain ⟨hpair⟩ := ConstructorStepProof.constructorStepPair n p stag etag ptag ctag atag len q l r
  hs he hp hc ha hlen hq hl hr ctx ctor ob nb ot nt
 have hboth := Hilbert.Local.mp (.mp (.base hpair) hbound) htail
 have hrowold := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hboth
 have hrest := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hboth
 have hrownew := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hrest
 have houtrel := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hrest
 obtain ⟨hco⟩ := StepTransportTaskProof.constructorInput p G stag ptag ctag l r hp hl hr oh ot tok ctor hk htok
 obtain ⟨hcn⟩ := StepTransportTaskProof.constructorInput p G stag ptag ctag l r hp hl hr nh nt tok ctor hnewkind htok
 have heq := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hold) (localTrans _ _ _ hco hrowold)
 have hresult := Hilbert.Local.mp (.base (.arithmetic (.succInjective _ _))) heq
 have hresultrel := Hilbert.Local.mp
  (.mp (.base (FinitePrefixProof.stackLeft len q l r (output ptag ctag atag ctor ob ot) result
    (output ptag ctag atag ctor nb nt))) (HistoryOrder.StepProof.localSym _ _ hresult)) houtrel
 have hnew := localTrans _ _ _ hcn hrownew
 have hw := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hnew) hresultrel
 exact ⟨.mp (.base (StepTransportWitnessProof.witnessIntro stag len q l r
  (HistoryLookup.consCall ctag nh nt) tok result (output ptag ctag atag ctor nb nt))) hw⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportConstructorProof
