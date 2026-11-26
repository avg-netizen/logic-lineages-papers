module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.EntryProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryKernel.EntryProof HistoryRuleSuffix

theorem entryValueExact {n ctx : Nat} (p : Program n) (tag ptag : Nat)
    (ht : (nodes p)[tag]? = some ⟨3,HistoryKernel.entry⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (context raw ref1 : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (entryValue tag (LiteralRawMP.lineValue ptag context raw ref1))
        (HistoryKernel.pairCall ptag context raw))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let R := HistoryKernel.pairCall ptag ref1 .zero
  let A := HistoryKernel.pairCall ptag .zero R
  let P := HistoryKernel.pairCall ptag .zero A
  let S := HistoryKernel.pairCall ptag (.succ (.succ .zero)) P
  let F := HistoryKernel.pairCall ptag raw S
  let line := LiteralRawMP.lineValue ptag context raw ref1
  have hpair := SixSol20261112.Fuel.Equations.functionChild p tag HistoryCodec.pair entryArguments ht
  have hcw := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.pair entryArguments ht 0
  have hrw := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.pair entryArguments ht 1
  have hcd := SixSol20261112.Fuel.Equations.functionChild p (contextWrapper tag) (HistoryDecoder.decoder false)
    (fun _ : Fin 1 => HistoryKernel.currentLine) hcw
  have hrd := SixSol20261112.Fuel.Equations.functionChild p (rawWrapper tag) (HistoryDecoder.decoder false)
    (fun _ : Fin 1 => applyOne (HistoryDecoder.decoder true) HistoryKernel.currentLine) hrw
  have hrr := SixSol20261112.Fuel.Equations.argumentChild p (rawWrapper tag) (HistoryDecoder.decoder false)
    (fun _ : Fin 1 => applyOne (HistoryDecoder.decoder true) HistoryKernel.currentLine) hrw 0
  have hrrd := SixSol20261112.Fuel.Equations.functionChild p (rawRightWrapper (rawWrapper tag))
    (HistoryDecoder.decoder true) (fun _ : Fin 1 => HistoryKernel.currentLine) hrr
  obtain ⟨hcontext⟩ := HistoryLookup.DestructorProof.decoderCrossPair p (contextWrapper tag+1) ptag false hcd hp context F
  obtain ⟨hfield⟩ := HistoryLookup.DestructorProof.decoderCrossPair p (rawRightWrapper (rawWrapper tag)+1) ptag true hrrd hp context F
  obtain ⟨hraw⟩ := HistoryLookup.DestructorProof.decoderCrossPair p (rawWrapper tag+1) ptag false hrd hp raw S
  have hr := localTrans _ _ _
    (LiteralRawMP.DispatcherSupportProof.callCongruence (T := T) (G := []) (rawWrapper tag+1)
      (call (rawRightWrapper (rawWrapper tag)+1) (line ::ᵥ nil) ::ᵥ nil)
      (F ::ᵥ nil) (by intro i; cases i using Fin.cases with
              | zero => exact .base hfield
              | succ i => exact Fin.elim0 i)) (.base hraw)
  obtain ⟨hcopy⟩ := HistoryDecoder.PairCongruenceProof.pairCopies p (tag+1) ptag hpair hp context raw
  exact ⟨Hilbert.Local.finish (localTrans _ _ _
    (HistoryIteratorSuffix.StepSuffixProof.pairCongruence (tag+1) _ _ context raw (.base hcontext) hr)
    (.base hcopy))⟩

theorem newHistoryExact {n ctx : Nat} (p : Program n) (tag ptag ctag : Nat)
    (ht : (nodes p)[tag]? = some ⟨3,HistoryKernel.someExtendedHistory⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (history context raw ref1 : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (newHistory tag history (LiteralRawMP.lineValue ptag context raw ref1))
        (HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag context raw) history))) := by
  have he := SixSol20261112.Fuel.Equations.argumentChild p tag .succ
    (fun _ : Fin 1 => HistoryKernel.extendedHistory) ht 0
  have hent := SixSol20261112.Fuel.Equations.argumentChild p (extendedWrapper tag)
    HistoryCodec.cons extendedArguments he 0
  obtain ⟨hv⟩ := entryValueExact p (entryWrapper tag) ptag hent hp context raw ref1
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p (outputConsTag tag) ctag 2
    HistoryCodec.cons (outputConsInstalled p tag ht) hc ctx
    (HistoryKernel.pairCall ptag context raw ::ᵥ history ::ᵥ nil)
  exact ⟨Hilbert.Local.finish (localTrans _ _ _
    (HistoryIteratorSuffix.StepSuffixProof.pairCongruence (outputConsTag tag) _ history _ history
      (.base hv) (.base (.logical (.reflexive history)))) (.base hcopy))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.EntryProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralMPRun.EntryProof
