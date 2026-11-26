module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionInductionProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.InstalledNodesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport StateRecursionProof Fusion FusionAlgebraProof

theorem internalFusion : Targets.InternalFusion := by
 intro n p scanTag atag hscan ha ctx tasks left right middle
 obtain ⟨itag,ltag,ptag,rtag,hi,hl,hp,hr⟩ := InstalledNodesProof.scanNodes p scanTag hscan
 obtain ⟨stag,hs⟩ := InstalledNodesProof.stepNode p itag hi
 have hv := HistoryAppend.TableEquationsProof.valueInstalled p (HistoryAppend.AppendEquationsProof.tableTag atag)
  (HistoryAppend.AppendEquationsProof.tableInstalled p atag ha)
 obtain ⟨hc,_,_,_,_,_⟩ := HistoryAppend.ValueEquationsProof.valueNodes p (HistoryAppend.PositiveProof.valueAt atag) hv
 let ctag := HistoryAppend.PositiveProof.outputConsTag atag
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (scanCall scanTag tasks left) (.succ middle)
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨hleft⟩ := ScanBindingProof.binding p scanTag itag ltag ptag rtag hscan hi hl hp hr tasks left
 have hprefix := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hleft)) hh
 obtain ⟨hall⟩ := ScanBindingProof.binding p scanTag itag ltag ptag rtag hscan hi hl hp hr tasks
  (HistoryAppend.appendCall atag left right)
 obtain ⟨hfuse⟩ := FusionInductionProof.fusionAll p itag ltag ptag rtag atag ctag stag hi hl hp hr ha hc hs
  left right (.succ tasks)
 have hright := scanCongruence (T := T) (G := [H]) itag ltag ptag rtag right right _ (.succ middle)
  (.base (.logical (.reflexive right))) hprefix
 obtain ⟨hfinal⟩ := ScanBindingProof.binding p scanTag itag ltag ptag rtag hscan hi hl hp hr middle right
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base hall)
  (localTrans _ _ _ (.base hfuse) (localTrans _ _ _ hright (.base (Support.equalitySymmetry _ _ hfinal))))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionProof
