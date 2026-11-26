module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.CanonicalProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.PairProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RawConstructorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport.ConstructorStepTargets
theorem kindNotTwo (T : Sentence → Prop) (ctx : Nat) (ctor : Constructor) :
 Nonempty (Derivation T (.neg (.equal (Term.numeral (n := ctx) (kind ctor)) (Term.numeral 2)))) := by
 cases ctor with
 | formula i => exact EmitterProof.oneNotTwo T ctx
 | term i =>
  let H : Formula ctx := .equal .zero (Term.numeral 2)
  let F : Formula ctx := .equal (Term.numeral 2) .zero
  have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
  have hm : Derivation T (.imp H F) := (HistoryOrder.StepProof.localSym _ _ hh).discharge.finish
  exact ⟨.mp (.mp (HistoryLengthConservation.StepSupportProof.contraposition H F) hm)
   (.arithmetic (.succNotZero (.succ .zero)))⟩
/-- Actual raw heads/token are normalized only using internal classifier
equalities, task relation and pair reconstruction; all18 constructors retained. -/
theorem transport {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (etag stepTag stag ptag ctag atag len q l r : Nat)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hstep : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hq : (nodes p)[q]? = some ⟨2,HistoryLookup.lookup⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (ctor : Constructor) (oh ot nh nt tok result raw : Term ctx)
 (hrel : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (taskRelation l r oh nh))
 (hrest : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (stackRelation len q l r ot nt))
 (hk : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (call l (oh ::ᵥ nil)) (Term.numeral (kind ctor))))
 (htok : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal tok (Term.numeral (token ctor))))
 (hold : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.stepCall stepTag (.succ (HistoryLookup.consCall ctag oh ot)) tok) (.succ result))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (results stag len q l r (HistoryLookup.consCall ctag nh nt)
   (UniformClosedSubstitutionEmit.emitCall etag (.succ (HistoryLookup.consCall ctag oh ot)) tok raw) result)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let depth := call r (nh ::ᵥ nil)
 obtain ⟨hne⟩ := kindNotTwo T ctx ctor
 obtain ⟨hkind⟩ := KindProof.ordinary T l r oh nh (Term.numeral (kind ctor)) hne
 have hnewkind := Hilbert.Local.mp (.mp (.base hkind) hrel) hk
 obtain ⟨hpairs⟩ := PairProof.canonical p G ptag l r (kind ctor) (kind ctor) hp hl hr oh nh hrel hk hnewkind
 have ho := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hpairs
 have hn := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hpairs
 have hot := TransportProof.cons ctag _ _ ot ho
 have hnt := TransportProof.cons ctag _ _ nt hn
 have hsarg := TransportProof.step stepTag _ _ tok (Term.numeral (token ctor)) hot htok
 obtain ⟨xtag,hx⟩ := RelationalSyntaxDepthTransport.ClosedScanInstallationProof.expandNode p stepTag hstep
 obtain ⟨hrow⟩ := RelationalSyntaxDepthTransport.ConstructorStepProof.stepAt p stepTag xtag ptag ctag atag
  hstep hx hp hc ha ctor (.succ depth) ot
 have hsucc := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hold) (localTrans _ _ _ hsarg (.base hrow))
 have hresult := Hilbert.Local.mp (.base (.arithmetic (.succInjective _ _))) hsucc
 have hemit := TransportProof.emit etag _ _ tok (Term.numeral (token ctor)) raw hot htok
 obtain ⟨hbody⟩ := CanonicalProof.allConstructors p G etag stepTag stag ptag ctag atag len q l r
  he hstep hs hp hc ha hlen hq hl hr ctor depth ot nt raw hrest
 exact TransportProof.finishCanonical stag len q l r _ _ _ _ result
  (output ptag ctag atag ctor (.succ depth) ot) (CanonicalProof.newOutput ptag ctag atag ctor depth nt)
  hnt hemit hresult hbody
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RawConstructorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.RawConstructorProof
