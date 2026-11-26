module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.DrainProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.StationaryProof

public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.ConversionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryLengthOffset (lengthCall)
open HistoryLengthOffset.OffsetSupportProof (substLength)
open HistoryIteratorSuffix.IterationProof (substIteration)
open IdleProof (substRun)

theorem fusionAt {n ctx : Nat} (p : Program n) itag (k : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,iterator k⟩) (first second code index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (iterationCall itag (.add first second) code index fuel)
        (iterationCall itag second (iterationCall itag first code index fuel) index fuel))) := by
  obtain ⟨hf⟩ := SixSol20261113.HistoryMachine.FusionProof.openFusion n p itag k hi ctx first code index fuel
  have h := atTerm (fusionTemplate itag first code index fuel) second hf
  simpa only [GorbowStandardInstances.instantiate,fusionTemplate,substituteFormula,substIteration,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using (show Nonempty (Derivation _ _) from ⟨h⟩)

theorem beyondLength {n ctx : Nat} (p : Program n) (itag ltag atag ptag ctag dtag droptag : Nat)
    (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,iterator (HistoryKernel.kernel v l a x)⟩)
    (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
    (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
    (hdrop : (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩) (code option index fuel gap : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (run itag ptag (.add (lengthCall ltag code) gap) option code index fuel)
        (run itag ptag (lengthCall ltag code) option code index fuel))) := by
  obtain ⟨hf⟩ := fusionAt p itag (HistoryKernel.kernel v l a x) hi (lengthCall ltag code) gap (state ptag option code) index fuel
  obtain ⟨hd0⟩ := DrainProof.internalLengthDrain v l a x n p itag ltag atag ptag ctag dtag droptag hi hl ha hp hc hd hdrop ctx code option index fuel
  obtain ⟨hs⟩ := StationaryProof.allStationary p itag dtag ptag v l a x hi hd hp gap
    (run itag ptag (lengthCall ltag code) option code index fuel) index fuel
  exact ⟨Logic.trans _ _ _ hf (.mp hs hd0)⟩

theorem internalBoundConversion : Targets.InternalBoundConversion := by
  intro v l a x n p itag ltag atag ptag ctag dtag droptag hi hl ha hp hc hd hdrop ctx code option index fuel
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := Formula.equal (run itag ptag code option code index fuel) (run itag ptag (lengthCall ltag code) option code index fuel)
  let C := liftTerm code
  let O := liftTerm option
  let I := liftTerm index
  let F := liftTerm fuel
  let H := Formula.equal C (.add (lengthCall ltag C) (.var (0 : Fin (ctx+1))))
  have hh : Hilbert.Local T (ctx+1) [H] H := .hypothesis List.mem_cons_self
  obtain ⟨he⟩ := beyondLength p itag ltag atag ptag ctag dtag droptag v l a x hi hl ha hp hc hd hdrop C O I F (.var 0)
  have hcong := StationaryProof.iterationCount itag C (.add (lengthCall ltag C) (.var 0)) (state ptag O C) I F hh
  have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
    simpa only [Q,C,O,I,F,GorbowPACore.weaken,substituteFormula,substRun,substLength,liftTerm,renameTerm,run] using
      Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ hcong (.base he)))
  obtain ⟨helim⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
  obtain ⟨hdata⟩ := LengthDataProof.lengthData n p ltag atag droptag ctag hl ha hdrop hc ctx code (.zero : Term ctx) .zero
  have hweak := Derivation.mp (.logical (.andLeft _ _)) (.mp (.logical (.andRight _ _)) hdata)
  have hweak' : Derivation T (.ex H) := by
    simpa only [HistoryBounds.weakBound,H,C,liftTerm,renameTerm,substLength] using hweak
  exact ⟨.mp helim hweak'⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.ConversionProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.ConversionProof
