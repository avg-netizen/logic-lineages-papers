module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.InvariantProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.OutputProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport LiteralRawMP.DispatcherSupportProof
open InvariantProof
/-- Actual old-state emission/append and output projection after a successful
old step. No new program node or frame-helper membership is introduced. -/
theorem advance {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ftag etag stepTag ptag ctag atag rtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (hstep : (nodes p)[stepTag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (token tokens oldTasks middle out raw : Term ctx)
 (hs : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.stepCall stepTag (.succ oldTasks) token) (.succ middle))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (outputAt ftag ptag rtag (HistoryLookup.consCall ctag token tokens) oldTasks out raw)
   (outputAt ftag ptag rtag tokens middle
    (HistoryAppend.appendCall atag out (UniformClosedSubstitutionEmit.emitCall etag (.succ oldTasks) token raw)) raw))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let nextOut := HistoryAppend.appendCall atag out (UniformClosedSubstitutionEmit.emitCall etag (.succ oldTasks) token raw)
 obtain ⟨_,hcons⟩ := UniformClosedSubstitutionRawFold.StatementChecks.exactRawRecursion
  n p ftag ptag ctag stepTag etag atag hf hp hc hstep he ha ctx token tokens (.succ oldTasks) out raw
 obtain ⟨hcons⟩ := hcons
 have hpair := callCongruence (T := T) (G := G) ptag
  (LiteralSyntaxStep.stepCall stepTag (.succ oldTasks) token ::ᵥ nextOut ::ᵥ nil)
  (.succ middle ::ᵥ nextOut ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hs
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive nextOut))
     | succ i => exact Fin.elim0 i)
 have hfold := callCongruence (T := T) (G := G) ftag
  (tokens ::ᵥ HistoryKernel.pairCall ptag (LiteralSyntaxStep.stepCall stepTag (.succ oldTasks) token) nextOut ::ᵥ raw ::ᵥ nil)
  (tokens ::ᵥ HistoryKernel.pairCall ptag (.succ middle) nextOut ::ᵥ raw ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive tokens))
   | succ i => cases i using Fin.cases with
     | zero => exact hpair
     | succ i => cases i using Fin.cases with
       | zero => exact .base (.logical (.reflexive raw))
       | succ i => exact Fin.elim0 i)
 have hwhole := localTrans _ _ _ (.base hcons) hfold
 exact ⟨callCongruence (T := T) (G := G) rtag _ _ (fun i => by
  cases i using Fin.cases with
  | zero => exact hwhole
  | succ i => exact Fin.elim0 i)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.OutputProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.OutputProof
