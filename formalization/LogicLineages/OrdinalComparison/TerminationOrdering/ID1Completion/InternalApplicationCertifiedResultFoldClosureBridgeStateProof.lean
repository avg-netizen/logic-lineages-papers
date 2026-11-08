module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeStateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertifiedResultFoldClosure
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalApplicationResultStackReturnSupportProof InternalApplicationResultStackCompositionStateProof
open InternalApplicationCertifiedResultFoldClosureBridgeBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalRawListRecursionSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

@[simp] theorem certifiedFoldRename {β : Type} (guard leaf : Program 1) (combine : Program 4)
    (out value : OTerm α) (j : α → β) :
    (certifiedFold guard leaf combine out value).relabel j =
      certifiedFold guard leaf combine (out.relabel j) (value.relabel j) := by
  simp only [certifiedFold,conjunctionRename,graph1Rename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel]

@[simp] theorem payloadFuelRename {β : Type} (payload : OTerm α) (j : α → β) :
    (payloadFuel payload).relabel j = payloadFuel (payload.relabel j) := by
  simp only [payloadFuel,InternalOriginalOrderSyntaxProof.addRelabel,sucRelabel]

theorem stateRecover (state out singleton : OTerm α)
    (hg : Nonempty (Derivation body Gamma (graph1 goodState (suc z) state)))
    (ho : Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.output out state)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode singleton out z))) :
    Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.emptyState state singleton)) := by
  apply queryCases ![InternalApplicationResultStack.status,InternalApplicationResultStack.work,
    InternalApplicationResultStack.results,InternalApplicationResultStack.tailOf InternalApplicationResultStack.results,
    InternalApplicationValidityStack.exactOne InternalApplicationResultStack.status,InternalUnpair.right]
    (Fin.cons state Fin.elim0) _
  intro β j ys Delta hj hq
  simp only [graph1Rename]
  simp only [consTermRename,emptyRename] at hq
  have hg' := renameInto hg j Delta hj
  have ho' := renameInto ho j Delta hj
  have hc' := renameInto hc j Delta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hg' ho'
  simp only [graph2Rename,zRelabel] at hc'
  let xs : Fin 1 → OTerm β := Fin.cons (state.relabel j) Fin.elim0
  have hb₀ := rejectZeroRecover _ _ (ys 4) xs (hq 4) hg'
  have hb₁ := rejectNonzeroRecover _ _ (ys 1) xs (hq 1) (andRight hb₀)
  have hb₂ := rejectZeroRecover _ _ (ys 2) xs (hq 2) (andRight hb₁)
  have hb₃ := rejectNonzeroRecover _ _ (ys 3) xs (hq 3) (andRight hb₂)
  have het := binaryRecover InternalEqualityTest.equalityTest InternalApplicationResultStack.status
    (InternalLessThan.constantOne 1) (ys 4) (ys 0) (suc z) xs (hq 4) (hq 0)
    (InternalLessThanSupportProof.oneConstantValue xs)
  have hs := outputTransport InternalApplicationResultStack.status (ys 0) (suc z) xs
    (equalityOfNonzero (ys 0) (suc z) (ys 4) het (andLeft hb₀)) (hq 0)
  have ho₀ := nonzeroBranchElim _ _ _ (out.relabel j) (ys 4) xs (hq 4) (andLeft hb₀) ho'
  have ho₁ := zeroBranchElim _ _ _ (out.relabel j) xs (andLeft hb₁) ho₀
  have ho₂ := nonzeroBranchElim _ _ _ (out.relabel j) (ys 2) xs (hq 2) (andLeft hb₂) ho₁
  have ho₃ := zeroBranchElim _ _ _ (out.relabel j) xs (andLeft hb₃) ho₂
  have hh := unaryRecover InternalListCodec.headCode InternalApplicationResultStack.results
    (out.relabel j) (ys 2) xs ho₃ (hq 2)
  have ht := unaryRecover InternalListCodec.tailCode InternalApplicationResultStack.results
    z (ys 2) xs (andLeft hb₃) (hq 2)
  have hcons := InternalListCodecDecompositionSupportProof.reconstructNonzero (ys 2)
    (out.relabel j) z (andLeft hb₂) hh ht
  have he := valueUnique InternalListCodec.consCode (ys 2) (singleton.relabel j)
    (Fin.cons (out.relabel j) (Fin.cons z Fin.elim0)) hcons hc'
  have hl := unaryRecover InternalUnpair.left InternalUnpair.right z (ys 5) xs (andLeft hb₁) (hq 5)
  have hr := unaryRecover InternalUnpair.right InternalUnpair.right (ys 2) (ys 5) xs (hq 2) (hq 5)
  have hempty := emptyStateValue (state.relabel j) (ys 5) (ys 2)
    (reconstructPair (ys 5) z (ys 2) hl hr)
    (reconstructPair (state.relabel j) (suc z) (ys 5) hs (hq 5))
  exact headTransport InternalApplicationResultStack.emptyState (state.relabel j)
    (ys 2) (singleton.relabel j) Fin.elim0 he hempty

theorem stateIntro (state out singleton : OTerm α)
    (he : Nonempty (Derivation body Gamma (graph1 InternalApplicationResultStack.emptyState state singleton)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode singleton out z))) :
    Nonempty (Derivation body Gamma
      (graph1 goodState (suc z) state ⊓ graph1 InternalApplicationResultStack.output out state)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have hl := emptyAsLive state singleton he
  have hs := sameAccept InternalApplicationResultStack.status (InternalLessThan.constantOne 1)
    (suc z) xs (liveStatus state z singleton hl) (InternalLessThanSupportProof.oneConstantValue xs)
  have hw := andLeft (liveStateFields state z singleton hl)
  have hr := andRight (liveStateFields state z singleton hl)
  have hd := InternalListCodecSupportProof.consDestruction singleton out z hc
  have hn := andRight (andRight hd)
  have ht := unaryValue InternalListCodec.tailCode InternalApplicationResultStack.results z singleton xs
    (andLeft (andRight hd)) hr
  have hh := unaryValue InternalListCodec.headCode InternalApplicationResultStack.results out singleton xs
    (andLeft hd) hr
  apply andIntro
  · apply successorBranchIntro _ _ _ (suc z) z xs hs
    apply zeroBranchIntro _ _ _ (suc z) xs hw
    apply nonzeroBranchIntro _ _ _ (suc z) singleton xs hr
      (by simpa only [equalEqn] using hn)
    exact zeroBranchIntro _ _ _ (suc z) xs ht (InternalLessThanSupportProof.oneConstantValue xs)
  · apply successorBranchIntro _ _ _ out z xs hs
    apply zeroBranchIntro _ _ _ out xs hw
    apply nonzeroBranchIntro _ _ _ out singleton xs hr
      (by simpa only [equalEqn] using hn)
    exact zeroBranchIntro _ _ _ out xs ht hh
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeStateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeStateProof
