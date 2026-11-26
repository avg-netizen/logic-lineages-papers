module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.StepProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open SixSol20261112.Fuel NamedArithmeticGraph
 theorem computes {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ptag stag etag atag
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (state out token raw : Term ctx) :
 Computes p G subStepCode (HistoryKernel.pairCall ptag state out ::ᵥ token ::ᵥ raw ::ᵥ nil)
  (HistoryKernel.pairCall ptag (LiteralSyntaxStep.stepCall stag state token)
   (HistoryAppend.appendCall atag out (UniformClosedSubstitutionEmit.emitCall etag state token raw))) := by
 let args := HistoryKernel.pairCall ptag state out ::ᵥ token ::ᵥ raw ::ᵥ nil
 have hstate : Computes p G syntaxState args state :=
  unary p G args (HistoryDecoder.decoder false) (.projection 0) _ _
   (projection p G args 0) (decoder p G ptag hp false state out)
 have hout : Computes p G output args out :=
  unary p G args (HistoryDecoder.decoder true) (.projection 0) _ _
   (projection p G args 0) (decoder p G ptag hp true state out)
 have hemit : Computes p G emitted args (UniformClosedSubstitutionEmit.emitCall etag state token raw) := by
  apply compose p G UniformClosedSubstitutionEmit.emitCode _ args (state ::ᵥ token ::ᵥ raw ::ᵥ nil) _ _
   (copies p G UniformClosedSubstitutionEmit.emitCode etag he _)
  intro i
  cases i using Fin.cases with
  | zero => exact hstate
  | succ i => cases i using Fin.cases with
    | zero => exact projection p G args 1
    | succ i => cases i using Fin.cases with
      | zero => exact projection p G args 2
      | succ i => exact Fin.elim0 i
 exact binary p G args HistoryCodec.pair _ _ _ _ _
  (binary p G args LiteralSyntaxStep.stepCode syntaxState (.projection 1) state token _
   hstate (projection p G args 1) (copies p G LiteralSyntaxStep.stepCode stag hs _))
  (binary p G args HistoryAppend.append output emitted out _ _ hout hemit
   (copies p G HistoryAppend.append atag ha _))
  (copies p G HistoryCodec.pair ptag hp _)
theorem exactSubStep : Targets.InternalSubStep := by
 intro n p qtag ptag stag etag atag hq hp hs he ha ctx state out token raw
 obtain ⟨h⟩ := computes p [] ptag stag etag atag hp hs he ha state out token raw qtag hq
 exact ⟨h.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.StepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.StepProof
