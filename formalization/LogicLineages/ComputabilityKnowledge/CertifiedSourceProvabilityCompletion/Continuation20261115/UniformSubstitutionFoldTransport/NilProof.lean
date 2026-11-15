module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.InvariantProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.NilProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open UniformSubstitutionChunkTransport InvariantProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem outputNil {n ctx : Nat} (p : Program n) (ftag ptag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hr : (nodes p)[rtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (oldTasks out raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (outputAt ftag ptag rtag .zero oldTasks out raw) out)) := by
 obtain ⟨hri,hi,hlen⟩ := UniformClosedSubstitutionRawFold.InstallationProof.installed p ftag hf
 obtain ⟨hn⟩ := UniformClosedSubstitutionRawFold.Proof.nilFold p ftag ptag _ _ _ hf hp hi hlen hri
  (HistoryKernel.pairCall ptag (.succ oldTasks) out) raw
 have heq := HistoryLookup.DestructorProof.unaryCallCongruence rtag _ _ hn
 obtain ⟨hd⟩ := HistoryLookup.DestructorProof.decoderCrossPair p rtag ptag true hr hp (.succ oldTasks) out
 exact ⟨Logic.trans _ _ _ heq hd⟩
/-- Empty input preserves actual accumulated output; original scan nil identifies
the old final stack before relation transport. No prefix validity is reflected. -/
theorem nil {n ctx : Nat} (p : Program n) (ftag vtag stag ptag len q l r : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (start raw oldTasks current out oldResult : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (property ftag vtag stag ptag len q l r .zero start raw oldTasks current out oldResult)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let V := RawReflexivityDispatcher.valid vtag raw
 let R := stackRelation len q l r oldTasks current
 let P := Formula.equal (LiteralSyntaxScan.scanCall stag start out) (.succ current)
 let S := Formula.equal (LiteralSyntaxScan.scanCall stag oldTasks .zero) (.succ oldResult)
 let G := [S,P,R,V]
 have hrel : Hilbert.Local T ctx G R := .hypothesis (by simp [G])
 have hprefix : Hilbert.Local T ctx G P := .hypothesis (by simp [G])
 have hold : Hilbert.Local T ctx G S := .hypothesis (by simp [G])
 obtain ⟨hnil⟩ := UniformSubstitutionChunkTransport.ScanProof.nil p stag ptag hs hp oldTasks
 have hsucc := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hnil)) hold
 have hresult := Hilbert.Local.mp (.base (.arithmetic (.succInjective _ _))) hsucc
 have hrel' := Hilbert.Local.mp (.mp (.base (UniformSubstitutionChunkTransport.FinitePrefixProof.stackLeft
  len q l r oldTasks oldResult current)) hresult) hrel
 obtain ⟨hout⟩ := outputNil p ftag ptag r hf hp hr oldTasks out raw
 have hscanArg := UniformSubstitutionIndexValidity.BranchProof.scanCongruence
  (T := T) (G := G) stag start _ _ (.base hout)
 have hscan := localTrans _ _ _ hscanArg hprefix
 have hb := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hscan) hrel'
 have hw := Hilbert.Local.mp (.base (UniformSubstitutionChunkTransport.WitnessProof.introResult
  stag len q l r start (outputAt ftag ptag r .zero oldTasks out raw) oldResult current)) hb
 exact ⟨hw.discharge.discharge.discharge.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.NilProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.NilProof
