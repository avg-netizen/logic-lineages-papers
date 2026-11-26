module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameInductionProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.InstalledNodesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport StateRecursionProof

theorem internalFrame : Targets.InternalFrame := by
 intro n p scanTag atag hscan ha ctx tasks raw out suffix
 obtain ⟨itag,ltag,ptag,rtag,hi,hl,hp,hr⟩ := InstalledNodesProof.scanNodes p scanTag hscan
 obtain ⟨stag,hs⟩ := InstalledNodesProof.stepNode p itag hi
 have hv := HistoryAppend.TableEquationsProof.valueInstalled p (HistoryAppend.AppendEquationsProof.tableTag atag)
  (HistoryAppend.AppendEquationsProof.tableInstalled p atag ha)
 obtain ⟨hc,hhead,_,_,_,_⟩ := HistoryAppend.ValueEquationsProof.valueNodes p (HistoryAppend.PositiveProof.valueAt atag) hv
 let ctag := HistoryAppend.PositiveProof.outputConsTag atag
 let dtag := HistoryAppend.PositiveProof.inputHeadTag atag+1
 have hd := Equations.functionChild p (HistoryAppend.PositiveProof.inputHeadTag atag)
  (HistoryDecoder.decoder false) (fun _ : Fin 1 => HistoryCodec.predecessor) hhead
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (scanCall scanTag tasks raw) (.succ out)
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hbind⟩ := ScanBindingProof.binding p scanTag itag ltag ptag rtag hscan hi hl hp hr tasks raw
 have hstate := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hbind)) hh
 obtain ⟨hframe⟩ := FrameInductionProof.frameAll p itag ltag ptag rtag atag ctag stag dtag hi hl hp hr ha hc hs hd raw tasks out suffix
 have result := Hilbert.Local.mp (.base hframe) hstate
 obtain ⟨hfinal⟩ := ScanBindingProof.binding p scanTag itag ltag ptag rtag hscan hi hl hp hr (HistoryAppend.appendCall atag tasks suffix) raw
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base hfinal) result))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FrameProof
