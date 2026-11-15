module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportConstructorProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportIndexAssemblyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportCasesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open ConstructorStepTargets ExpansionCasesTargets ExpansionCasesSupportProof
/-- Pure original disjunction elimination over a finite constructor list. -/
theorem foldCases {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
 (xs : List Constructor) (arm : Constructor → Formula ctx) (last Q : Formula ctx)
 (hc : ∀ ctor, Nonempty (Hilbert.Local T ctx G (.imp (arm ctor) Q)))
 (hi : Hilbert.Local T ctx G (.imp last Q)) :
 Nonempty (Hilbert.Local T ctx G (.imp (xs.foldr (fun c rest => .disj (arm c) rest) last) Q)) := by
 induction xs with
 | nil => exact ⟨hi⟩
 | cons c xs ih =>
  obtain ⟨hc'⟩ := hc c
  obtain ⟨hr⟩ := ih
  exact ⟨.mp (.mp (.base (.logical (.orElim _ _ Q))) hc') hr⟩
/-- All19 original successful expansion arms are discharged internally. Raw
heads and token remain arbitrary; no constructor/index choice is a premise. -/
theorem classifiedTransport {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (stag etag ptag ctag atag dtag len q l r : Nat)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (oh ot nh nt tok result added : Term ctx)
 (hh : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (taskRelation l r oh nh))
 (htail : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (stackRelation len q l r ot nt))
 (hex : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.expandCall etag oh tok) (.succ added)))
 (hold : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.stepCall stag (.succ (HistoryLookup.consCall ctag oh ot)) tok) (.succ result))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (StepTransportTargets.witnesses stag len q l r (HistoryLookup.consCall ctag nh nt) tok result)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := StepTransportTargets.witnesses stag len q l r (HistoryLookup.consCall ctag nh nt) tok result
 have hctors : ∀ ctor, Nonempty (Hilbert.Local T ctx G
  (.imp (constructorCase ptag ctag l r oh tok added ctor) Q)) := by
  intro ctor
  let C := constructorCase ptag ctag l r oh tok added ctor
  have hcase : Hilbert.Local T ctx (C :: G) C := .hypothesis List.mem_cons_self
  have hk := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hcase
  have hb := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hcase
  have ht := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hb
  obtain ⟨hout⟩ := StepTransportConstructorProof.constructorTransport p (C :: G)
   stag etag ptag ctag atag len q l r hs he hp hc ha hlen hq hl hr oh ot nh nt tok result ctor
   (push C hh) (push C htail) hk ht (push C hold)
  exact ⟨hout.discharge⟩
 let I := indexCase dtag l r oh tok added
 have hi : Hilbert.Local T ctx (I :: G) I := .hypothesis List.mem_cons_self
 have hk := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hi
 have hb := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hi
 have hg := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hb
 obtain ⟨helim⟩ := StepTransportIndexAssemblyProof.eliminateOld p stag etag ctag atag dtag len q l r
  hs he hc ha hd hl hr oh ot nh nt tok result
 have hout := Hilbert.Local.mp (.mp (.mp (.mp (.mp (.base helim) hg) (push I hh)) (push I htail)) hk) (push I hold)
 obtain ⟨hall⟩ := foldCases constructors (constructorCase ptag ctag l r oh tok added) I Q hctors hout.discharge
 obtain ⟨hclass⟩ := ExpansionCasesProof.expansionSuccessCases n p etag ptag ctag dtag l r
  he hp hc hd hl hr ctx oh tok added
 exact ⟨.mp hall (.mp (.base hclass) hex)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportCasesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.StepTransportCasesProof
