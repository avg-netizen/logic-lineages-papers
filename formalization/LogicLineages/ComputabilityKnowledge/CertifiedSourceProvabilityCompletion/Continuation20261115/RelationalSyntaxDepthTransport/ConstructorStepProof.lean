module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ConstructorTaskProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ConstructorExpansionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ConstructorStepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 SixSol20261112.Fuel
open ConstructorStepTargets

theorem stepAt {n ctx : Nat} (p : Program n) (stag etag ptag ctag atag : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (ctor : Constructor) (binder rest : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (LiteralSyntaxStep.stepCall stag (input ptag ctag ctor binder rest) (Term.numeral (token ctor)))
  (.succ (output ptag ctag atag ctor binder rest)))) := by
 obtain ⟨hx⟩ := ConstructorExpansionProof.constructorAt p [] ptag ctag hp hc binder ctor etag he
 obtain ⟨hsx⟩ := LiteralSyntaxStep.StepProof.internalPrepend n p stag etag ctag atag hs he hc ha ctx
  (LiteralSyntaxStep.taskCall ptag (kind ctor) binder) rest (Term.numeral (token ctor))
  (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder ctor))
 exact ⟨.mp hsx (Hilbert.Local.finish hx)⟩

/-- Full exact finite constructor-step integration. Inputs remain runtime terms;
only the explicit original constructor-token family is finite. -/
theorem constructorStepPair : ConstructorStepTargets.InternalConstructorStepPair := by
 intro n p stag etag ptag ctag atag len q l r hs he hp hc ha hl hq hleft hright ctx ctor oldBound newBound rest newRest
 let T := GorbowPRNumeralCalculation.Theory p
 let H := HistoryBounds.weakBound oldBound newBound
 let R := stackRelation len q l r rest newRest
 let G := [R,H]
 have hh : Hilbert.Local T ctx G H := .hypothesis (by simp [G])
 have hr : Hilbert.Local T ctx G R := .hypothesis (by simp [G])
 have hrows := ConstructorTaskProof.taskRows p G ptag l r hp hleft hright ctor oldBound newBound hh
 obtain ⟨hout⟩ := FinitePrefixProof.finitePrefixAppend n p len q l r ctag atag hl hq hc ha ctx G
  (tasks ptag oldBound ctor) (tasks ptag newBound ctor) rest newRest hrows ⟨hr⟩
 obtain ⟨ho⟩ := stepAt p stag etag ptag ctag atag hs he hp hc ha ctor oldBound rest
 obtain ⟨hn⟩ := stepAt p stag etag ptag ctag atag hs he hp hc ha ctor newBound newRest
 have hb := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) (.base hn)) hout
 have hall := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) (.base ho)) hb
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hall))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ConstructorStepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ConstructorStepProof
