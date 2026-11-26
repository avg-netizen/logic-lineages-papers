module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ChildTransferProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryGuardQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryRootProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.BinaryAtChildrenProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (symm refl)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open Continuation20261114 Continuation20261115 Continuation20261116
open OriginalRawSyntaxTransport Induction
open OriginalCodeBoundsConstructors.BinaryRootProof (constructor)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalEnumerationFields.Boolean.ListCasesProof (memberHead memberTail)
open InternalApplicationCertificateConstructorsSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
theorem guardsAtLists (cons : Bool) (n : Nat) (raw typ head tail rest children : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 (constructor cons) raw typ head tail)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest tail z)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode children head rest))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) head)) ∧
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)) := by
  have hchildren := ArgumentEntriesChildren.InternalProof.internalBinary body alpha Delta cons raw typ head tail rest children hc hr hl
  exact ⟨OriginalDecodedDependencyClosure.ChildrenProof.childrenClosed n body alpha Delta raw children head hg hchildren (memberHead children head rest hl),
    OriginalDecodedDependencyClosure.ChildrenProof.childrenClosed n body alpha Delta raw children tail hg hchildren
      (memberTail children head rest tail hl (memberHead rest tail z hr))⟩

theorem guards (cons : Bool) (n : Nat) (raw typ head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 (constructor cons) raw typ head tail)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw))) :
    Nonempty (Derivation body Delta
      (graph1 (OriginalCodeValidityGuard.check n) (suc z) head ⊓
       graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases OriginalExchangeBoundsPreservation.EntryGuardQueriesProof.queries ![head,tail] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![head,tail] i).relabel j) = ![head.relabel j,tail.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  simp only [conjunctionRename,graph1Rename,sucRelabel,zRelabel]
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  rw [graph3Rename] at hcj
  simp only [graph1Rename,sucRelabel,zRelabel] at hgj
  obtain ⟨hr,hl⟩ := OriginalExchangeBoundsPreservation.EntryGuardQueriesProof.recover (head.relabel j) (tail.relabel j) ys hq
  obtain ⟨hh,ht⟩ := guardsAtLists cons n (raw.relabel j) (typ.relabel j)
    (head.relabel j) (tail.relabel j) (ys 0) (ys 1) hcj hgj hr hl
  exact andIntro hh ht

theorem branch (cons side : Bool) (n : Nat) (arity : Fin n → Nat)
 (left right lm rm lc ld rc rd child window context symbols types : OTerm alpha)
 (hlc : Nonempty (Derivation body Delta (graph3 (constructor cons) left lm lc ld)))
 (hrc : Nonempty (Derivation body Delta (graph3 (constructor cons) right rm rc rd)))
 (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
 (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
 (hmeta : Nonempty (Derivation body Delta (eqn lm rm)))
 (hsibling : Nonempty (Derivation body Delta (eqn (if side then lc else ld) (if side then rc else rd))))
 (hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child (if side then ld else lc) (if side then rd else rc))))
 (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) child window)))
 (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
 (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
 Nonempty (Derivation body Delta (PlainAwareStructuralDefinitions.Transfer n arity
  (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
  cons left right context)) := by
 have hlgc := guards cons n left lm lc ld hlc hlg
 have hrgc := guards cons n right rm rc rd hrc hrg
 have hsmall : Nonempty (Derivation body Delta
  (InternalLessThan.strictLess lc left ⊓ InternalLessThan.strictLess ld left)) := by
  cases cons
  · exact OriginalTypedEnumerationDepthBound.DescentProof.application left lm lc ld hlc
  · exact OriginalTypedEnumerationDepthBound.DescentProof.cons left lm lc ld hlc
 have hchildedge : Nonempty (Derivation body Delta
  (edge n arity (if side then ld else lc) (if side then rd else rc) child window)) := by
  cases side
  · exact andIntro hpair (andIntro (andLeft hlgc) (andIntro (andLeft hrgc) he))
  · exact andIntro hpair (andIntro (andRight hlgc) (andIntro (andRight hrgc) he))
 have hless : Nonempty (Derivation body Delta (InternalLessThan.strictLess (if side then ld else lc) left)) := by
  cases side
  · exact andLeft hsmall
  · exact andRight hsmall
 have ht := ChildTransferProof.fromBelow n arity (if side then cons else false)
  left (if side then ld else lc) (if side then rd else rc) child window context symbols types henv hchildedge ih hless
 have hrc' : Nonempty (Derivation body Delta (graph3 (constructor cons) right lm
  (if side then lc else rc) (if side then rd else ld))) := by
  apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 3 Delta _ right ![rm,rc,rd]
   ![lm,if side then lc else rc,if side then rd else ld] _ hrc
  intro i
  fin_cases i
  · rw [onEquality]
    obtain ⟨h⟩ := hmeta
    exact ⟨symm h⟩
  · rw [onEquality]
    cases side
    · exact ⟨refl _⟩
    · obtain ⟨h⟩ := hsibling
      exact ⟨symm h⟩
  · rw [onEquality]
    cases side
    · obtain ⟨h⟩ := hsibling
      exact ⟨symm h⟩
    · exact ⟨refl _⟩
 cases cons <;> cases side
 · exact PlainAwareStructuralClosureProof.applicationFunction n arity _ _ body alpha Delta
    left right lm lc rc ld context hlc hrc' hlg hrg ht
 · exact PlainAwareStructuralClosureProof.applicationArgument n arity _ _ body alpha Delta
    left right lm lc ld rd context hlc hrc' hlg hrg ht
 · exact PlainAwareStructuralClosureProof.argumentsHead n arity _ _ body alpha Delta
    left right lm lc rc ld context hlc hrc' hlg hrg ht
 · exact PlainAwareStructuralClosureProof.argumentsTail n arity _ _ body alpha Delta
    left right lm lc ld rd context hlc hrc' hlg hrg ht

open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
theorem atChildren (cons : Bool) (n : Nat) (arity : Fin n → Nat)
 (left right lm rm lc ld rc rd node first last window context symbols types : OTerm alpha)
 (hlc : Nonempty (Derivation body Delta (graph3 (constructor cons) left lm lc ld)))
 (hrc : Nonempty (Derivation body Delta (graph3 (constructor cons) right rm rc rd)))
 (hfirst : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first lc rc)))
 (hlast : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last ld rd)))
 (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
 (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
 (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
 Nonempty (Derivation body Delta (PlainAwareStructuralDefinitions.Transfer n arity
  (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
  cons left right context)) := by
 have hp := andLeft hedge
 have hlg := andLeft (andRight hedge)
 have hrg := andLeft (andRight (andRight hedge))
 have he := andRight (andRight (andRight hedge))
 have hr := (OriginalDecodedBinaryRecurrence.Proof.binaryRecurrence n arity body alpha Delta cons
  left right lm rm lc ld rc rd node first last window hlc hrc hp hfirst hlast).mp he
 apply OriginalTypedDecoderInternalBranchProof.orCases (andRight (andRight hr))
 · have hb : Nonempty (Derivation body ((eqn ld rd ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) first window) :: Delta)
    (eqn ld rd ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) first window)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
   exact branch cons false n arity left right lm rm lc ld rc rd first window context symbols types
    (withHyp hlc _) (withHyp hrc _) (withHyp hlg _) (withHyp hrg _) (withHyp (andLeft (andRight hr)) _)
    (andLeft hb) (withHyp hfirst _) (andRight hb) (withHyp henv _) (withHyp ih _)
 · have hb : Nonempty (Derivation body ((eqn lc rc ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) last window) :: Delta)
    (eqn lc rc ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) last window)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
   exact branch cons true n arity left right lm rm lc ld rc rd last window context symbols types
    (withHyp hlc _) (withHyp hrc _) (withHyp hlg _) (withHyp hrg _) (withHyp (andLeft (andRight hr)) _)
    (andLeft hb) (withHyp hlast _) (andRight hb) (withHyp henv _) (withHyp ih _)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.BinaryAtChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.BinaryAtChildrenProof
