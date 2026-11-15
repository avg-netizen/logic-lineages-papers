module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.StepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.TickProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LiteralSyntaxStep.StepSupportProof SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix
theorem tickNil {n ctx : Nat} (p : Program n) ptag
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (state raw : Term ctx) :
 Computes p [] tick (HistoryKernel.pairCall ptag .zero state ::ᵥ raw ::ᵥ nil)
  (HistoryKernel.pairCall ptag .zero state) := by
 let args := HistoryKernel.pairCall ptag .zero state ::ᵥ raw ::ᵥ nil
 exact chooseZero p [] args remaining (.projection 0) _ _
  (unary p [] args (HistoryDecoder.decoder false) (.projection 0) _ _
   (projection p [] args 0) (decoder p [] ptag hp false .zero state))
  (projection p [] args 0)
theorem tickCons {n ctx : Nat} (p : Program n) ptag ctag stag etag atag
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hs : (nodes p)[stag]? = some ⟨2,LiteralSyntaxStep.stepCode⟩)
 (he : (nodes p)[etag]? = some ⟨3,UniformClosedSubstitutionEmit.emitCode⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (token tokens state out raw : Term ctx) :
 Computes p [] tick
  (HistoryKernel.pairCall ptag (HistoryLookup.consCall ctag token tokens)
   (HistoryKernel.pairCall ptag state out) ::ᵥ raw ::ᵥ nil)
  (HistoryKernel.pairCall ptag tokens
   (HistoryKernel.pairCall ptag (LiteralSyntaxStep.stepCall stag state token)
    (HistoryAppend.appendCall atag out (UniformClosedSubstitutionEmit.emitCall etag state token raw)))) := by
 let row := HistoryLookup.consCall ctag token tokens
 let old := HistoryKernel.pairCall ptag state out
 let args := HistoryKernel.pairCall ptag row old ::ᵥ raw ::ᵥ nil
 have hrem : Computes p [] remaining args row :=
  unary p [] args (HistoryDecoder.decoder false) (.projection 0) _ _
   (projection p [] args 0) (decoder p [] ptag hp false row old)
 have hacc : Computes p [] accumulator args old :=
  unary p [] args (HistoryDecoder.decoder true) (.projection 0) _ _
   (projection p [] args 0) (decoder p [] ptag hp true row old)
 have htail := unary p [] args HistoryLookup.tail remaining row tokens hrem (tailCons p [] ctag hc token tokens)
 have hhead := unary p [] args HistoryLookup.head remaining row token hrem (headCons p [] ctag hc token tokens)
 let next := HistoryKernel.pairCall ptag (LiteralSyntaxStep.stepCall stag state token)
  (HistoryAppend.appendCall atag out (UniformClosedSubstitutionEmit.emitCall etag state token raw))
 have hadv : Computes p [] advanced args next := by
  apply compose p [] subStepCode _ args (old ::ᵥ token ::ᵥ raw ::ᵥ nil) next _
   (StepProof.computes p [] ptag stag etag atag hp hs he ha state out token raw)
  intro i
  cases i using Fin.cases with
  | zero => exact hacc
  | succ i => cases i using Fin.cases with
    | zero => exact hhead
    | succ i => cases i using Fin.cases with
      | zero => exact projection p [] args 1
      | succ i => exact Fin.elim0 i
 have hout := binary p [] args HistoryCodec.pair (applyOne HistoryLookup.tail remaining) advanced
  tokens next _ htail hadv (copies p [] HistoryCodec.pair ptag hp _)
 let cp := ctag + argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
 let pv := HistoryKernel.pairCall cp token tokens
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx token tokens
 have hpositive : Computes p [] remaining args (.succ pv) :=
  changeValue p [] remaining args row _ hrem (.base hcons)
 exact choosePositive p [] args remaining (.projection 0) _ pv _ hpositive hout
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.TickProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.TickProof
