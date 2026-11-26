module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalSourceInversionSupportProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalGraphCompositionFunctionalityProof InternalBetaTotalityProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRawListRecursionSyntaxProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

 theorem withHyp {phi : Formula alpha} (h : Nonempty (Derivation body Gamma phi)) (p : Formula alpha) :
    Nonempty (Derivation body (p :: Gamma) phi) := by
  obtain ⟨h⟩ := h
  exact ⟨addHyp h p⟩

 theorem iffRefl (p : Formula alpha) : Nonempty (Derivation body Gamma (p.iff p)) :=
  ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))⟩

 theorem iffSymm {p q : Formula alpha} (h : Nonempty (Derivation body Gamma (p.iff q))) :
    Nonempty (Derivation body Gamma (q.iff p)) := andIntro (andRight h) (andLeft h)

 theorem iffTrans {p q r : Formula alpha}
    (h : Nonempty (Derivation body Gamma (p.iff q)))
    (k : Nonempty (Derivation body Gamma (q.iff r))) :
    Nonempty (Derivation body Gamma (p.iff r)) := by
  obtain ⟨h⟩ := h
  obtain ⟨k⟩ := k
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction (Derivation.implicationElimination
      (Derivation.conjunctionLeft (addHyp k p)) (Derivation.implicationElimination
        (Derivation.conjunctionLeft (addHyp h p)) (Derivation.hypothesis List.mem_cons_self))))
    (Derivation.implicationIntroduction (Derivation.implicationElimination
      (Derivation.conjunctionRight (addHyp h r)) (Derivation.implicationElimination
        (Derivation.conjunctionRight (addHyp k r)) (Derivation.hypothesis List.mem_cons_self))))⟩

@[simp] theorem variableSubst {beta : Type} (out typ index gamma : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (OriginalVariableDecoder.graph out typ index gamma).subst (fun a => emb (ts a)) =
      OriginalVariableDecoder.graph (out.subst ts) (typ.subst ts) (index.subst ts) (gamma.subst ts) := by
  simp only [OriginalVariableDecoder.graph,programSubst,consTermSubst,emptySubst]

 theorem variableInputs (out typ index gamma index' gamma' : OTerm alpha)
    (hi : Nonempty (Derivation body Gamma (eqn index index')))
    (hg : Nonempty (Derivation body Gamma (eqn gamma gamma')))
    (h : Nonempty (Derivation body Gamma (OriginalVariableDecoder.graph out typ index gamma))) :
    Nonempty (Derivation body Gamma (OriginalVariableDecoder.graph out typ index' gamma')) := by
  apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 3 Gamma _ out
    (Fin.cons typ (Fin.cons index (Fin.cons gamma Fin.elim0)))
    (Fin.cons typ (Fin.cons index' (Fin.cons gamma' Fin.elim0))) _ h
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q))) i
  · rw [onEquality]
    exact ⟨refl typ⟩
  · rw [onEquality]
    exact hi
  · rw [onEquality]
    exact hg

 theorem variableIffInputs (out typ index gamma index' gamma' : OTerm alpha)
    (hi : Nonempty (Derivation body Gamma (eqn index index')))
    (hg : Nonempty (Derivation body Gamma (eqn gamma gamma'))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ index gamma).iff
        (OriginalVariableDecoder.graph out typ index' gamma'))) := by
  obtain ⟨hf⟩ := variableInputs out typ index gamma index' gamma'
    (withHyp hi _) (withHyp hg _) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hi⟩ := hi
  obtain ⟨hg⟩ := hg
  obtain ⟨hb⟩ := variableInputs out typ index' gamma' index gamma
    (withHyp ⟨symm hi⟩ _) (withHyp ⟨symm hg⟩ _) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableSupportProof
