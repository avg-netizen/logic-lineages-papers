module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseZeroInductionBindingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseChildQueriesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseZeroKeepProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseFoundProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchQueryCasesProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseZeroIdentityProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof (headTransport)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc eqn emb eqnRelabel zRelabel bindEmbedding liftBind varBind)
open InternalTagArithmeticSupportProof (symm trans sucNeZeroApply)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open InternalBinderTransportProof InternalTermSubstitutionProof
open NumberedWindowInternalScratchQueryCasesProof (notRename queryCases)
open SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof (orCases)
open NumberedWindowInternalLiteralScratchErase (state)
open NumberedWindowInternalLiteralScratchEraseFlagsConsProof (flags)
open NumberedWindowInternalLiteralScratchEraseBranchFlagsProof (headHit tailHit)
open NumberedWindowInternalLiteralScratchEraseZeroKeepProof (keepSame)
open NumberedWindowInternalLiteralScratchEraseCoordinatesProof (nilCoordinates)
open NumberedWindowInternalLiteralScratchEraseZeroInductionDefinitions
open NumberedWindowInternalLiteralScratchEraseZeroInductionSyntaxProof
open NumberedWindowInternalLiteralScratchEraseZeroInductionBindingProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph


private theorem oneImpossible (raw bit rest : OTerm alpha)
    (one : Nonempty (Derivation body Delta (eqn bit (suc z)))) :
    Nonempty (Derivation body Delta (zeroIdentity raw bit rest)) := by
  let Z := eqn bit z
  obtain ⟨e⟩ := withHyp one Z
  have h : Derivation body (Z :: Delta) Z := Derivation.hypothesis List.mem_cons_self
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply (trans (symm e) h)))⟩

private theorem consZeroIdentity (list head tail needle acc tailBit rest actual bit remaining : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc tailBit rest)))
    (ih : Nonempty (Derivation body Delta (zeroIdentity tail tailBit rest)))
    (ha : Nonempty (Derivation body Delta (graph2 state actual list needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual bit remaining))) :
    Nonempty (Derivation body Delta (zeroIdentity list bit remaining)) := by
  have b := NumberedWindowInternalLiteralScratchEraseFoundProof.actualResult tail needle acc tailBit rest ht hp
  have b' : Nonempty (Derivation body Delta (eqn tailBit z ⊔ eqn tailBit (suc z))) := andLeft b
  apply orCases b'
  · let E := eqn tailBit z
    have e : Nonempty (Derivation body (E :: Delta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp0 := headTransport InternalPairing.pairing acc tailBit z (Fin.cons rest Fin.elim0) e (withHyp hp E)
    have idTail : Nonempty (Derivation body (E :: Delta) (eqn rest tail)) := by
      obtain ⟨h⟩ := withHyp ih E
      obtain ⟨e⟩ := e
      exact ⟨Derivation.implicationElimination h e⟩
    let H := eqn head needle
    apply formulaCases H
    · exact oneImpossible list bit remaining (headHit list head tail needle acc rest actual bit remaining
        (withHyp (withHyp hc E) H) (withHyp (withHyp ht E) H) (withHyp hp0 H)
        ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp (withHyp ha E) H) (withHyp (withHyp hap E) H))
    · let N := H.not
      have hn : Nonempty (Derivation body (N :: E :: Delta) N) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      let Z := eqn bit z
      have h := keepSame list head tail needle acc rest actual bit remaining
        (withHyp (withHyp hc E) N) (withHyp (withHyp ht E) N) (withHyp hp0 N) (withHyp idTail N) hn
        (withHyp (withHyp ha E) N) (withHyp (withHyp hap E) N)
      obtain ⟨d⟩ := withHyp (andRight h) Z
      exact ⟨Derivation.implicationIntroduction d⟩
  · let E := eqn tailBit (suc z)
    have e : Nonempty (Derivation body (E :: Delta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp1 := headTransport InternalPairing.pairing acc tailBit (suc z) (Fin.cons rest Fin.elim0) e (withHyp hp E)
    exact oneImpossible list bit remaining (tailHit list head tail needle acc rest actual bit remaining
      (withHyp hc E) (withHyp ht E) hp1 (withHyp ha E) (withHyp hap E))

theorem nonzero (raw needle acc bit rest : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not)) :
    Nonempty (Derivation body Delta (zeroIdentity raw bit rest)) := by
  apply queryCases NumberedWindowInternalLiteralScratchEraseChildQueriesProof.queries ![raw,needle] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![raw,needle] i).relabel j) = ![raw.relabel j,needle.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t)) i
  rw [hx] at hq
  rw [zeroRename]
  have hvj := renameInto hv j Theta hj
  have hpj := renameInto hp j Theta hj
  have ihj := renameInto ih j Theta hj
  have hnj := renameInto hn j Theta hj
  rw [graph2Rename] at hvj hpj
  rw [belowRawRename] at ihj
  simp only [notRename,eqnRelabel,zRelabel] at hnj
  obtain ⟨hc,ht,hpair⟩ := NumberedWindowInternalLiteralScratchEraseChildQueriesProof.recover (raw.relabel j) (needle.relabel j) ys hnj hq
  have hsmall := InternalListCodecDecompositionSupportProof.consTailDescent (raw.relabel j) (ys 0) (ys 1) hc
  have htail := belowRawApply (raw.relabel j) (ys 1) (needle.relabel j) (ys 2) (ys 3) (ys 4)
    ihj hsmall (andIntro ht hpair)
  exact consZeroIdentity (raw.relabel j) (ys 0) (ys 1) (needle.relabel j) (ys 2) (ys 3) (ys 4)
    (acc.relabel j) (bit.relabel j) (rest.relabel j) hc ht hpair htail hvj hpj

theorem atRaw (raw needle acc bit rest : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (zeroIdentity raw bit rest)) := by
  apply formulaCases (eqn raw z)
  · have he : Nonempty (Derivation body ((eqn raw z) :: Delta) (eqn raw z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv0 := headTransport state acc raw z (Fin.cons needle Fin.elim0) he (withHyp hv _)
    have pairNil := nilCoordinates needle acc bit rest hv0 (withHyp hp _)
    let Z := eqn bit z
    obtain ⟨er⟩ := withHyp (andRight pairNil) Z
    obtain ⟨eqraw⟩ := withHyp he Z
    exact ⟨Derivation.implicationIntroduction (trans er (symm eqraw))⟩
  · exact nonzero raw needle acc bit rest (withHyp hv _) (withHyp hp _) (withHyp ih _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem step (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  apply atRawIntro raw
  let x : Fin 4 → OTerm (alpha ⊕ Fin 4) := fun i => .var (.inr i)
  let f := fields (raw.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3)
  let Theta : List (Formula (alpha ⊕ Fin 4)) := f :: Delta.map (fun q => q.relabel Sum.inl)
  have hf : Nonempty (Derivation body Theta f) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hi : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 4) ∈ Theta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih Sum.inl Theta hi
  rw [belowRawRename] at ihj
  obtain ⟨d⟩ := atRaw (raw.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3)
    (andLeft hf) (andRight hf) ihj
  exact ⟨Derivation.implicationIntroduction d⟩

theorem allRaw (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw raw)) :=
  rawInduction raw (fun _ _ r ih => step r ih)

theorem actualResult (raw needle acc bit rest : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest))) :
    Nonempty (Derivation body Delta (zeroIdentity raw bit rest)) :=
  atRawApply raw needle acc bit rest (allRaw raw) (andIntro hv hp)
/-- Actual zero flag preserves the exact original open raw tape. -/
theorem exactZeroIdentity (raw needle acc bit rest : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (hz : Nonempty (Derivation body Delta (eqn bit z))) :
    Nonempty (Derivation body Delta (eqn rest raw)) := by
  obtain ⟨d⟩ := actualResult raw needle acc bit rest hv hp
  obtain ⟨e⟩ := hz
  exact ⟨Derivation.implicationElimination d e⟩

#print axioms actualResult
#print axioms exactZeroIdentity
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseZeroIdentityProof
