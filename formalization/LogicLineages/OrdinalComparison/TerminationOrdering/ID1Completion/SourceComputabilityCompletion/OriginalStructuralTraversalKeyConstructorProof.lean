module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyCongruenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyConstructorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalStructuralClassKeyDefinitions OriginalStructuralClassKeyActiveProof
open OriginalHereditaryValidityInternalNodeSupportProof (weakenProof)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem applicationAtCoreValues (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (value other d e fn arg otherFn otherArg fOut aOut parameter mark : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (Active p H G W value parameter)))
    (hb : Nonempty (Derivation body Delta (Active p H G W other parameter)))
    (hf : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.ApplicationFields value d e fn arg)))
    (hg : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.ApplicationFields other d e otherFn otherArg)))
    (hfn : Nonempty (Derivation body Delta (graph2 (core p H G W) fOut fn parameter)))
    (hofn : Nonempty (Derivation body Delta (graph2 (core p H G W) fOut otherFn parameter)))
    (harg : Nonempty (Derivation body Delta (graph2 (core p H G W) aOut arg parameter)))
    (hoarg : Nonempty (Derivation body Delta (graph2 (core p H G W) aOut otherArg parameter)))
    : Nonempty (Derivation body Delta
      ((graph2 (key p H G W) mark other parameter).iff
        (graph2 (key p H G W) mark value parameter))) := by
  have forward : Nonempty (Derivation body
      (graph2 (key p H G W) mark other parameter :: Delta)
      (graph2 (key p H G W) mark value parameter)) := by
    have inc : ∀ f, f ∈ Delta → f ∈ graph2 (key p H G W) mark other parameter :: Delta :=
      fun _ h => List.mem_cons_of_mem _ h
    have hcore := keyToCore p H G W other mark parameter
      (weakenProof hb inc) ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hctor := OriginalLambdaTraversalInternalApplicationProof.applicationForward
      (OriginalLambdaTraversalSelection.leaf (prior p H G W).base p.window)
      other d e otherFn otherArg parameter fOut aOut mark
      (weakenProof hg inc) (weakenProof hofn inc) (weakenProof hoarg inc) hcore
    have hnew := OriginalLambdaTraversalInternalApplicationProof.applicationBackward
      (OriginalLambdaTraversalSelection.leaf (prior p H G W).base p.window)
      value d e fn arg parameter fOut aOut mark
      (weakenProof hf inc) (weakenProof hfn inc) (weakenProof harg inc) hctor
    exact coreToKey p H G W value mark parameter (weakenProof ha inc) hnew
  have backward : Nonempty (Derivation body
      (graph2 (key p H G W) mark value parameter :: Delta)
      (graph2 (key p H G W) mark other parameter)) := by
    have inc : ∀ f, f ∈ Delta → f ∈ graph2 (key p H G W) mark value parameter :: Delta :=
      fun _ h => List.mem_cons_of_mem _ h
    have hcore := keyToCore p H G W value mark parameter
      (weakenProof ha inc) ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hctor := OriginalLambdaTraversalInternalApplicationProof.applicationForward
      (OriginalLambdaTraversalSelection.leaf (prior p H G W).base p.window)
      value d e fn arg parameter fOut aOut mark
      (weakenProof hf inc) (weakenProof hfn inc) (weakenProof harg inc) hcore
    have hnew := OriginalLambdaTraversalInternalApplicationProof.applicationBackward
      (OriginalLambdaTraversalSelection.leaf (prior p H G W).base p.window)
      other d e otherFn otherArg parameter fOut aOut mark
      (weakenProof hg inc) (weakenProof hofn inc) (weakenProof hoarg inc) hctor
    exact coreToKey p H G W other mark parameter (weakenProof hb inc) hnew
  obtain ⟨hfwd⟩ := forward
  obtain ⟨hbwd⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hfwd) (Derivation.implicationIntroduction hbwd)⟩

theorem lambdaAtCoreValues (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (value other d e child otherChild childOut parameter childParameter mark : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (Active p H G W value parameter)))
    (hb : Nonempty (Derivation body Delta (Active p H G W other parameter)))
    (hf : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields value d e child parameter childParameter)))
    (hg : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields other d e otherChild parameter childParameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (core p H G W) childOut child childParameter)))
    (hoc : Nonempty (Derivation body Delta (graph2 (core p H G W) childOut otherChild childParameter)))
    : Nonempty (Derivation body Delta
      ((graph2 (key p H G W) mark other parameter).iff
        (graph2 (key p H G W) mark value parameter))) := by
  have forward : Nonempty (Derivation body
      (graph2 (key p H G W) mark other parameter :: Delta)
      (graph2 (key p H G W) mark value parameter)) := by
    have inc : ∀ f, f ∈ Delta → f ∈ graph2 (key p H G W) mark other parameter :: Delta :=
      fun _ h => List.mem_cons_of_mem _ h
    have hcore := keyToCore p H G W other mark parameter
      (weakenProof hb inc) ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hctor := OriginalLambdaTraversalInternalLambdaProof.lambdaForward
      (OriginalLambdaTraversalSelection.leaf (prior p H G W).base p.window)
      other d e otherChild parameter childParameter childOut mark
      (weakenProof hg inc) (weakenProof hoc inc) hcore
    have hnew := OriginalLambdaTraversalInternalLambdaProof.lambdaBackward
      (OriginalLambdaTraversalSelection.leaf (prior p H G W).base p.window)
      value d e child parameter childParameter childOut mark
      (weakenProof hf inc) (weakenProof hc inc) hctor
    exact coreToKey p H G W value mark parameter (weakenProof ha inc) hnew
  have backward : Nonempty (Derivation body
      (graph2 (key p H G W) mark value parameter :: Delta)
      (graph2 (key p H G W) mark other parameter)) := by
    have inc : ∀ f, f ∈ Delta → f ∈ graph2 (key p H G W) mark value parameter :: Delta :=
      fun _ h => List.mem_cons_of_mem _ h
    have hcore := keyToCore p H G W value mark parameter
      (weakenProof ha inc) ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hctor := OriginalLambdaTraversalInternalLambdaProof.lambdaForward
      (OriginalLambdaTraversalSelection.leaf (prior p H G W).base p.window)
      value d e child parameter childParameter childOut mark
      (weakenProof hf inc) (weakenProof hc inc) hcore
    have hnew := OriginalLambdaTraversalInternalLambdaProof.lambdaBackward
      (OriginalLambdaTraversalSelection.leaf (prior p H G W).base p.window)
      other d e otherChild parameter childParameter childOut mark
      (weakenProof hg inc) (weakenProof hoc inc) hctor
    exact coreToKey p H G W other mark parameter (weakenProof hb inc) hnew
  obtain ⟨hfwd⟩ := forward
  obtain ⟨hbwd⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hfwd) (Derivation.implicationIntroduction hbwd)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyConstructorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyConstructorProof
