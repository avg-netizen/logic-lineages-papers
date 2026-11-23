module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseFlagsInductionBindingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseChildQueriesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchQueryCasesProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseFoundProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof (headTransport)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc eqn emb eqnRelabel zRelabel bindEmbedding liftBind varBind)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open InternalBinderTransportProof InternalTermSubstitutionProof
open NumberedWindowInternalScratchQueryCasesProof (notRename queryCases)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalLiteralScratchErase (state)
open NumberedWindowInternalLiteralScratchEraseFlagsConsProof (flags consFlags nilFlags)
open NumberedWindowInternalLiteralScratchEraseFlagsInductionDefinitions
open NumberedWindowInternalLiteralScratchEraseFlagsInductionSyntaxProof
open NumberedWindowInternalLiteralScratchEraseFlagsInductionBindingProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nonzero (raw needle acc bit rest : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not)) :
    Nonempty (Derivation body Delta (flags raw needle bit)) := by
  apply queryCases NumberedWindowInternalLiteralScratchEraseChildQueriesProof.queries ![raw,needle] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![raw,needle] i).relabel j) = ![raw.relabel j,needle.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t)) i
  rw [hx] at hq
  rw [flagsRename]
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
  exact consFlags (raw.relabel j) (ys 0) (ys 1) (needle.relabel j) (ys 2) (ys 3) (ys 4)
    (acc.relabel j) (bit.relabel j) (rest.relabel j) hc ht hpair htail hvj hpj

theorem atRaw (raw needle acc bit rest : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (flags raw needle bit)) := by
  apply formulaCases (eqn raw z)
  · have he : Nonempty (Derivation body ((eqn raw z) :: Delta) (eqn raw z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv0 := headTransport state acc raw z (Fin.cons needle Fin.elim0) he (withHyp hv _)
    obtain ⟨hnil⟩ := nilFlags needle acc bit rest hv0 (withHyp hp _)
    obtain ⟨he⟩ := he
    have d := Derivation.equalityElimination
      (flags (.var (.inr 0)) (needle.relabel Sum.inl) (bit.relabel Sum.inl))
      (emb z) (emb raw) (symm he)
    simp only [instantiate,bindEmbedding,flagsSubst,liftBind,varBind] at d
    exact ⟨d hnil⟩
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
    Nonempty (Derivation body Delta (flags raw needle bit)) :=
  atRawApply raw needle acc bit rest (allRaw raw) (andIntro hv hp)
/-- A true original scratch membership ensures that the actual literal erase
reports one on arbitrary open inputs. State and coordinate graphs are actual. -/
theorem found (raw needle acc bit rest : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (hm : Nonempty (Derivation body Delta (memberGraph raw needle))) :
    Nonempty (Derivation body Delta (eqn bit (suc z))) := by
  obtain ⟨d⟩ := andRight (actualResult raw needle acc bit rest hv hp)
  obtain ⟨m⟩ := hm
  exact ⟨Derivation.implicationElimination d m⟩

#print axioms actualResult
#print axioms found

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseFoundProof
