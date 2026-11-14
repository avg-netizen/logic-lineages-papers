module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.RetainedCompatibilityObstructionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticProgramProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.RetainedCompatibilitySoundnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro)
open SourceComputabilityFormulaSupportProof (numeral numeralTruth)
open SixSol20261113.Erasure
open EvaluatorErasureDefinitions EvaluatorErasureSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Semantic interpretation of the unchanged compiled graph. This is used
only in the soundness direction to refute a proposed internal admissible rule. -/
theorem programTruth {n : Nat} {alpha : Type} (R : Program n)
    (out : OTerm alpha) (xs : Fin n → OTerm alpha) (Q : Nat → Prop) (v : alpha → Nat) :
    realize Q (programGraph R out xs) v ↔
      evaluate R (List.Vector.ofFn (fun i => (xs i).realize v)) = out.realize v := by
  rw [programGraph,InternalGraphComposition.graph,PositiveArithmeticOperatorsSupportProof.embeddingTruth]
  exact OrdinaryArithmeticProgramProof.appliedProgramGraphTruth R out xs v

theorem binaryTruth {alpha : Type} (R : Program 2) (out left parameter : OTerm alpha)
    (Q : Nat → Prop) (v : alpha → Nat) :
    realize Q (graph2 R out left parameter) v ↔
      evaluate R (List.Vector.ofFn ![left.realize v,parameter.realize v]) = out.realize v := by
  rw [graph2,programTruth]
  rfl

/-- A genuine admitted native collision refutes the UNRESTRICTED internal
rule by soundness. No semantic fact is introduced as an internal derivation:
every input derivation below is a literal hypothesis in Delta. -/
theorem incompatibleOfCollision (R : Program 2) (H G : Program 1) (M W : Program 2)
    (leftCode rightCode parameterCode : Nat)
    (hleft : evaluate (OriginalUniverseDecoder.source H G M W)
      (List.Vector.ofFn ![leftCode,parameterCode]) = 1)
    (hright : evaluate (OriginalUniverseDecoder.source H G M W)
      (List.Vector.ofFn ![rightCode,parameterCode]) = 1)
    (he : evaluate (OriginalHereditaryEvaluatorDefinitions.evaluator R)
      (List.Vector.ofFn ![leftCode,parameterCode]) =
      evaluate (OriginalHereditaryEvaluatorDefinitions.evaluator R)
        (List.Vector.ofFn ![rightCode,parameterCode]))
    (hne : evaluate R (List.Vector.ofFn ![leftCode,parameterCode]) ≠
      evaluate R (List.Vector.ofFn ![rightCode,parameterCode])) :
    ¬ EvaluatorConstructorCongruenceDefinitions.UniformRetainedCompatibility R H G M W := by
  intro compat
  let body : Positive (Fin 1) := .predicate (.var 0)
  let Q := standardLeastPredicate body
  let left : OTerm (Fin 5) := .var 0
  let right : OTerm (Fin 5) := .var 1
  let parameter : OTerm (Fin 5) := .var 2
  let value : OTerm (Fin 5) := .var 3
  let common : OTerm (Fin 5) := .var 4
  let S := OriginalUniverseDecoder.source H G M W
  let E := OriginalHereditaryEvaluatorDefinitions.evaluator R
  let Delta : List (Formula (Fin 5)) :=
    [graph2 S (numeral 1) left parameter,
      graph2 S (numeral 1) right parameter,
      graph2 E common left parameter,
      graph2 E common right parameter,
      graph2 R value left parameter]
  have hsleft : Nonempty (Derivation body Delta (graph2 S (numeral 1) left parameter)) :=
    ⟨.hypothesis (by simp [Delta])⟩
  have hsright : Nonempty (Derivation body Delta (graph2 S (numeral 1) right parameter)) :=
    ⟨.hypothesis (by simp [Delta])⟩
  have heleft : Nonempty (Derivation body Delta (graph2 E common left parameter)) :=
    ⟨.hypothesis (by simp [Delta])⟩
  have heright : Nonempty (Derivation body Delta (graph2 E common right parameter)) :=
    ⟨.hypothesis (by simp [Delta])⟩
  have hrleft : Nonempty (Derivation body Delta (graph2 R value left parameter)) :=
    ⟨.hypothesis (by simp [Delta])⟩
  have ha : Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)) :=
    andIntro hsleft (andIntro hsright
      (sameIntro R left right parameter common (andIntro heleft heright)))
  have hout := compat body (Fin 5) Delta left right parameter value ha hrleft
  let v : Fin 5 → Nat := ![leftCode,rightCode,parameterCode,
    evaluate R (List.Vector.ofFn ![leftCode,parameterCode]),
    evaluate E (List.Vector.ofFn ![leftCode,parameterCode])]
  have hDelta : ∀ phi, phi ∈ Delta → realize Q phi v := by
    intro phi hphi
    simp only [Delta,List.mem_cons,List.mem_singleton] at hphi
    rcases hphi with rfl | rfl | rfl | rfl | rfl
    · apply (binaryTruth S (numeral 1) left parameter Q v).mpr
      simpa [S,left,parameter,v,numeralTruth] using hleft
    · apply (binaryTruth S (numeral 1) right parameter Q v).mpr
      simpa [S,right,parameter,v,numeralTruth] using hright
    · apply (binaryTruth E common left parameter Q v).mpr
      rfl
    · apply (binaryTruth E common right parameter Q v).mpr
      simpa [E,common,right,parameter,v] using he.symm
    · apply (binaryTruth R value left parameter Q v).mpr
      rfl
  have htruth := InternalCalculusProof.actualInternalCalculusSoundness body Q
    (InternalCalculusSupportProof.actualStandardLeastModel body) (Fin 5) Delta
    (graph2 R value right parameter) hout v hDelta
  have hvalue := (binaryTruth R value right parameter Q v).mp htruth
  apply hne
  simpa [value,right,parameter,v] using hvalue.symm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.RetainedCompatibilitySoundnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.RetainedCompatibilitySoundnessProof
