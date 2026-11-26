module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate.DispatcherProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate.EntryProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryKernel.EntryProof

theorem entryValueExact {n ctx : Nat} (p : Program n) (tag ptag : Nat)
 (ht : (nodes p)[tag]? = some ⟨3,HistoryKernel.entry⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (context raw payload : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (entryValue tag (HistoryKernel.pairCall ptag context (HistoryKernel.pairCall ptag raw payload)))
   (HistoryKernel.pairCall ptag context raw))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let rest := HistoryKernel.pairCall ptag raw payload
 let line := HistoryKernel.pairCall ptag context rest
 have hpair := Equations.functionChild p tag HistoryCodec.pair entryArguments ht
 have hcw := Equations.argumentChild p tag HistoryCodec.pair entryArguments ht 0
 have hrw := Equations.argumentChild p tag HistoryCodec.pair entryArguments ht 1
 have hcd := Equations.functionChild p (contextWrapper tag) (HistoryDecoder.decoder false)
  (fun _ : Fin 1 => HistoryKernel.currentLine) hcw
 have hrd := Equations.functionChild p (rawWrapper tag) (HistoryDecoder.decoder false)
  (fun _ : Fin 1 => applyOne (HistoryDecoder.decoder true) HistoryKernel.currentLine) hrw
 have hrr := Equations.argumentChild p (rawWrapper tag) (HistoryDecoder.decoder false)
  (fun _ : Fin 1 => applyOne (HistoryDecoder.decoder true) HistoryKernel.currentLine) hrw 0
 have hrrd := Equations.functionChild p (rawRightWrapper (rawWrapper tag)) (HistoryDecoder.decoder true)
  (fun _ : Fin 1 => HistoryKernel.currentLine) hrr
 obtain ⟨hcontext⟩ := HistoryLookup.DestructorProof.decoderCrossPair p (contextWrapper tag+1) ptag false hcd hp context rest
 obtain ⟨hfield⟩ := HistoryLookup.DestructorProof.decoderCrossPair p (rawRightWrapper (rawWrapper tag)+1) ptag true hrrd hp context rest
 obtain ⟨hraw⟩ := HistoryLookup.DestructorProof.decoderCrossPair p (rawWrapper tag+1) ptag false hrd hp raw payload
 have hr := localTrans _ _ _
  (LiteralRawMP.DispatcherSupportProof.callCongruence (T := T) (G := []) (rawWrapper tag+1)
   (call (rawRightWrapper (rawWrapper tag)+1) (line ::ᵥ nil) ::ᵥ nil) (rest ::ᵥ nil)
   (by intro i; cases i using Fin.cases with
       | zero => exact .base hfield
       | succ i => exact Fin.elim0 i)) (.base hraw)
 obtain ⟨hcopy⟩ := HistoryDecoder.PairCongruenceProof.pairCopies p (tag+1) ptag hpair hp context raw
 exact ⟨Hilbert.Local.finish (localTrans _ _ _
  (HistoryIteratorSuffix.StepSuffixProof.pairCongruence (tag+1) _ _ context raw (.base hcontext) hr) (.base hcopy))⟩

theorem newHistoryExact {n ctx : Nat} (p : Program n) (tag ptag ctag : Nat)
 (ht : (nodes p)[tag]? = some ⟨3,HistoryKernel.someExtendedHistory⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (history context raw payload : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (newHistory tag history (HistoryKernel.pairCall ptag context (HistoryKernel.pairCall ptag raw payload)))
   (HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag context raw) history))) := by
 have he := Equations.argumentChild p tag .succ (fun _ : Fin 1 => HistoryKernel.extendedHistory) ht 0
 have hent := Equations.argumentChild p (extendedWrapper tag) HistoryCodec.cons extendedArguments he 0
 obtain ⟨hv⟩ := entryValueExact p (entryWrapper tag) ptag hent hp context raw payload
 obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p (outputConsTag tag) ctag 2
  HistoryCodec.cons (outputConsInstalled p tag ht) hc ctx (HistoryKernel.pairCall ptag context raw ::ᵥ history ::ᵥ nil)
 exact ⟨Hilbert.Local.finish (localTrans _ _ _
  (HistoryIteratorSuffix.StepSuffixProof.pairCongruence (outputConsTag tag) _ history _ history
   (.base hv) (.base (.logical (.reflexive history)))) (.base hcopy))⟩

theorem quotedNewHistory {k n ctx : Nat} (t : Term k) (old arithmetic : Program 1) (x : Program 3)
 (p : Program n) (I : Installation p t old arithmetic x) (values : List.Vector (Term ctx) k)
 (tag : Nat) (ht : (nodes p)[tag]? = some ⟨3,HistoryKernel.someExtendedHistory⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (newHistory tag .zero (line I.qtag values))
   (HistoryLookup.consCall I.ctag (HistoryKernel.pairCall I.ptag .zero (raw I.etag values)) .zero))) := by
 obtain ⟨hq⟩ := DispatcherProof.quoteEquation t old arithmetic x p I values
 have hcong := Logic.unary (newHistory tag .zero (.var (0 : Fin 1))) _ _ hq
 simp only [newHistory,entryValue,HistoryKernel.pairCall,HistoryLookup.consCall,
  Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,GorbowSubstitution.substitute,Fin.cases_zero] at hcong
 obtain ⟨hv⟩ := newHistoryExact p tag I.ptag I.ctag ht I.hp I.hc .zero .zero (raw I.etag values)
  (DispatcherProof.payload I.ptag I.ctag (LiteralTemplateQuote.quoteCall I.ttag values))
 exact ⟨Logic.trans _ _ _ hcong hv⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate.EntryProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.TwoSol20261113.ReflexivityCertificate.EntryProof
