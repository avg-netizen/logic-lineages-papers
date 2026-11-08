module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationValidityStackAppend InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppendSyntaxProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationValidityStackAppendListProof InternalApplicationValidityStackAppendRunProof
open InternalApplicationValidityStackAppendInductionSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalAdditionCancellationProof InternalOriginalOrderSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphChoiceProof
open InternalPositiveUnfoldingSupportProof InternalBetaTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem withHyp {phi : Formula α} (h : Nonempty (Derivation body Gamma phi)) (p : Formula α) :
    Nonempty (Derivation body (p :: Gamma) phi) := by
  obtain ⟨h⟩ := h
  exact ⟨addHyp h p⟩

theorem formulaCases (p psi : Formula α)
    (hp : Nonempty (Derivation body (p :: Gamma) psi))
    (hn : Nonempty (Derivation body (p.not :: Gamma) psi)) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hn⟩ := hn
  exact ⟨disjunctionElimination (excludedMiddle p)
    (Derivation.implicationIntroduction hp) (Derivation.implicationIntroduction hn)⟩

theorem rowApply (node leaf : Program 1) (count second frontWork suffix joined : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (appendRow node leaf count)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (successfulWork node leaf count frontWork)))
    (hs : Nonempty (Derivation body Gamma (successfulWork node leaf second suffix))) :
    Nonempty (Derivation body Gamma
      (successfulWork node leaf (OrdinaryArithmetic.addTerm count second) joined)) := by
  have h := actualFiniteUniversalElimination body α 4 Gamma (appendBody node leaf count)
    (fun i => emb (![second,frontWork,suffix,joined] i)) hrow
  rw [appendBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := andIntro ha (andIntro hf hs)
  exact ⟨Derivation.implicationElimination h hp⟩

theorem emptyCore (node leaf : Program 1) (count second frontWork suffix joined : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn frontWork z)))
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hs : Nonempty (Derivation body Gamma (successfulWork node leaf second suffix))) :
    Nonempty (Derivation body Gamma
      (successfulWork node leaf (OrdinaryArithmetic.addTerm count second) joined)) := by
  have hz := headTransport append joined frontWork z (Fin.cons suffix Fin.elim0) he ha
  obtain ⟨hjoined⟩ := appendZeroRecover joined suffix hz
  have hpad := successPadding node leaf second count suffix hs
  have hcount := countTransport node leaf (add second count) (add count second) suffix
    ⟨commutativity second count⟩ hpad
  exact workTransport node leaf (add count second) suffix joined ⟨symm hjoined⟩ hcount

theorem zeroCore (node leaf : Program 1) (second frontWork suffix joined : OTerm α)
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (successfulWork node leaf z frontWork)))
    (hs : Nonempty (Derivation body Gamma (successfulWork node leaf second suffix))) :
    Nonempty (Derivation body Gamma
      (successfulWork node leaf (OrdinaryArithmetic.addTerm z second) joined)) :=
  emptyCore node leaf z second frontWork suffix joined (zeroWork node leaf frontWork hf) ha hs

theorem zeroRow (node leaf : Program 1) :
    Nonempty (Derivation body Gamma (appendRow node leaf z)) := by
  unfold appendRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let second : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let frontWork : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let suffix : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let joined : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let A := graph2 append joined frontWork suffix ⊓
    (successfulWork node leaf z frontWork ⊓ successfulWork node leaf second suffix)
  obtain ⟨d⟩ := zeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) node leaf second frontWork suffix joined
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [appendBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
