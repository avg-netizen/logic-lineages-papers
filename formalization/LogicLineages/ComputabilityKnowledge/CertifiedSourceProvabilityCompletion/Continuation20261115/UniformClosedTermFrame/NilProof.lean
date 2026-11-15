module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.InvariantProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.AppendRightProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.NilProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport InvariantProof
open LiteralRawMP.DispatcherSupportProof
/-- Nil case of the actual framed invariant: scanner success empties the old
stack, the checked relation empties its target prefix, and arbitrary output is
preserved by the now-paid original right-empty append law. -/
theorem nil {n ctx : Nat} (p : Program n) (ftag stag ptag ctag atag len q l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (hlen : (nodes p)[len]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (raw oldTasks newTasks rest out : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (property ftag stag ptag ctag atag len q l r .zero raw oldTasks newTasks rest out)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let E := EntriesLogic.entries q (LiteralSyntaxStep.taskCall ptag 0 (.zero : Term ctx)) oldTasks
 let R := RelationalSyntaxDepthTransport.stackRelation len q l r oldTasks newTasks
 let S := Formula.equal (LiteralSyntaxScan.scanCall stag oldTasks .zero) (.succ .zero)
 let G := [S,R,E]
 have hrel : Hilbert.Local T ctx G R := .hypothesis (by simp [G])
 have hscan : Hilbert.Local T ctx G S := .hypothesis List.mem_cons_self
 obtain ⟨hnil⟩ := UniformSubstitutionChunkTransport.ScanProof.nil p stag ptag hs hp oldTasks
 have hold := Hilbert.Local.mp (.base (.arithmetic (.succInjective _ _)))
  (localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hnil)) hscan)
 have hrel0 := Hilbert.Local.mp (.mp (.base (RelationalSyntaxDepthTransport.FinitePrefixProof.stackLeft
  len q l r oldTasks .zero newTasks)) hold) hrel
 obtain ⟨hz⟩ := RelationalSyntaxDepthTransport.LengthZeroProof.relatedEmpty p len q l r ctag hlen hc newTasks
 have hnew := Hilbert.Local.mp (.base hz) hrel0
 have happ := callCongruence (T := T) (G := G) atag
  (newTasks ::ᵥ rest ::ᵥ List.Vector.nil) ((.zero : Term ctx) ::ᵥ rest ::ᵥ List.Vector.nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hnew
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive rest))
     | succ i => exact Fin.elim0 i)
 obtain ⟨hzrest⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx rest
 have hrest := localTrans _ _ _ happ (.base hzrest)
 have hsucc := localUnary (.succ (.var 0)) _ _ hrest
 have hsucc' : Hilbert.Local T ctx G
  (.equal (.succ (HistoryAppend.appendCall atag newTasks rest)) (.succ rest)) := by
  simpa only [GorbowStandardInstances.instantiate,GorbowSubstitution.substitute,Fin.cases_zero] using hsucc
 obtain ⟨hright⟩ := AppendRightProof.rightNil p atag ha out
 have hpairs := HistoryIteratorSuffix.ReconstructionProof.pairCongruence (T := T) (G := G) ptag
  (.succ (HistoryAppend.appendCall atag newTasks rest)) out (.succ rest) (HistoryAppend.appendCall atag out .zero)
  hsucc' (.base (Support.equalitySymmetry _ _ hright))
 obtain ⟨hr0,hi,hl⟩ := UniformClosedSubstitutionRawFold.InstallationProof.installed p ftag hf
 obtain ⟨hf0⟩ := UniformClosedSubstitutionRawFold.Proof.nilFold p ftag ptag _ _ _ hf hp hi hl hr0
  (HistoryKernel.pairCall ptag (.succ (HistoryAppend.appendCall atag newTasks rest)) out) raw
 have hout := localTrans _ _ _ (.base hf0) hpairs
 exact ⟨hout.discharge.discharge.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.NilProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.NilProof
