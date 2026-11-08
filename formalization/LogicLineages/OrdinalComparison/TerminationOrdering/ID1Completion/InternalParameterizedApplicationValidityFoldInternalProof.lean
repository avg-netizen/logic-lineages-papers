module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalParameterizedApplicationValidityFold
open InternalParameterizedApplicationValidityFoldTargets
open InternalParameterizedApplicationResultFoldTotality
open InternalApplicationValidityClosure InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Literal quinary combine accepts the original codomain node and two one
outputs. The parameter is coordinate four, not part of a reconstructed code. -/
theorem combineAccepted (node : Program 2) (d e parameter : OTerm α)
    (hn : Nonempty (Derivation body Gamma (graph2 node (suc z) e parameter))) :
    Nonempty (Derivation body Gamma
      (programGraph (combineP node) (suc z)
        (Fin.cons d (Fin.cons e (Fin.cons (suc z)
          (Fin.cons (suc z) (Fin.cons parameter Fin.elim0))))))) := by
  let xs : Fin 5 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons (suc z)
    (Fin.cons (suc z) (Fin.cons parameter Fin.elim0))))
  have hn' : Nonempty (Derivation body Gamma (programGraph (nodeAtP node) (suc z) xs)) := by
    apply compositionValue node ![.projection 1, .projection 4] (suc z) xs
      (Fin.cons e (Fin.cons parameter Fin.elim0)) hn
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i
    · exact projectionValue 1 xs
    · exact projectionValue 4 xs
  exact conjunctionAccept (nodeAtP node)
    (InternalAcceptance.conjunction (.projection 2) (.projection 3)) xs hn'
    (conjunctionAccept (.projection 2) (.projection 3) xs
      (projectionValue 2 xs) (projectionValue 3 xs))

/-- Instantiate the exact internal totality/application equivalence. Neither
child success nor semantic evaluation is supplied to this derivation. -/
theorem actualOriginalParameterizedValidityFoldApplicationClosure :
    ActualOriginalParameterizedValidityFoldApplicationClosure := by
  intro body node oldLeaf α Gamma arrow d e fp ap fn arg parent parameter
  let premise := applicationConstructors arrow d e fp ap fn arg parent ⊓
    (graph2 node (suc z) e parameter ⊓
      (graph2 (validatorP node oldLeaf) (suc z) fn parameter ⊓
        graph2 (validatorP node oldLeaf) (suc z) arg parameter))
  have hp : Nonempty (Derivation body (premise :: Gamma) premise) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hg : Nonempty (Derivation body (premise :: Gamma)
      (graph2 openingGuardP (suc z) parent parameter)) :=
    InternalLessThanSupportProof.oneConstantValue (Fin.cons parent (Fin.cons parameter Fin.elim0))
  have inputs := andIntro (andLeft hp)
    (andIntro hg (andIntro (andLeft (andRight (andRight hp)))
      (andRight (andRight (andRight hp)))))
  obtain ⟨he⟩ :=
    InternalParameterizedApplicationResultFoldTotalityProof.actualOriginalParameterizedResultFoldApplicationEquation
      body openingGuardP (leafP oldLeaf) (combineP node) α (premise :: Gamma)
      arrow d e fp ap fn arg parent (suc z) (suc z) (suc z) parameter
  obtain ⟨hi⟩ := inputs
  have hb := Derivation.conjunctionRight (Derivation.implicationElimination he hi)
  obtain ⟨hc⟩ := combineAccepted node d e parameter (andLeft (andRight hp))
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hb hc)⟩

/-- Source-to-target is actual conjunction recovery at arbitrary symbolic p,
not a reflection of the external calibration or a validity premise. -/
theorem actualOriginalParameterizedValidityFoldSourceImpliesTarget :
    ActualOriginalParameterizedValidityFoldSourceImpliesTarget := by
  intro body oldSource oldTarget member α Gamma value parameter
  let premise := graph2 (sourceP oldSource oldTarget member) (suc z) value parameter
  have hp : Nonempty (Derivation body (premise :: Gamma) premise) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨ht⟩ := andLeft (conjunctionRecover (targetP oldTarget)
    (universeP oldSource member) (Fin.cons value (Fin.cons parameter Fin.elim0)) hp)
  exact ⟨Derivation.implicationIntroduction ht⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldInternalProof
