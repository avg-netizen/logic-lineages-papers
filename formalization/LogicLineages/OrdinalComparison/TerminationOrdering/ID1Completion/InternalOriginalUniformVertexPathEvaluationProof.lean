module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathPrimitiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathEvaluationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedQuotientApplication
open InternalOriginalUniformVertexPath
open InternalOriginalUniformVertexPathPrimitiveProof
open InternalOriginalUniformDescentSelection (Data selectedTyped)
open InternalOriginalUniformParameterLeaves (parameterCode)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local instance] Classical.propDecidable

theorem functionTypedEvaluation (data : Data) (v : List.Vector Nat 5) :
    evaluate (functionTyped data) v = evaluate (selectedTyped data)
      (List.Vector.ofFn ![v.get 4,1 + Nat.pair (v.get 1) (v.get 2),v.get 0]) := by
  change evaluate (selectedTyped data)
    (List.Vector.ofFn fun i : Fin 3 => evaluate
      ((![Program.projection 4,consOf (.projection 1) (.projection 2),.projection 0] :
        Fin 3 → Program 5) i) v) = _
  congr 1
  apply List.Vector.ext
  intro i
  exact Fin.cases rfl (Fin.cases (consOfEvaluation (.projection 1) (.projection 2) v)
    (Fin.cases rfl (fun q => Fin.elim0 q))) i

theorem argumentTypedEvaluation (data : Data) (v : List.Vector Nat 5) :
    evaluate (argumentTyped data) v = evaluate (selectedTyped data)
      (List.Vector.ofFn ![v.get 3,v.get 1,v.get 0]) := by
  change evaluate (selectedTyped data)
    (List.Vector.ofFn fun i : Fin 3 => evaluate
      ((![Program.projection 3,.projection 1,.projection 0] : Fin 3 → Program 5) i) v) = _
  congr 1

theorem activationEvaluation (data : Data) (v : List.Vector Nat 5) :
    evaluate (activation data) v =
      if Active data (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4) then 1 else 0 := by
  rw [activation,conjunctionEvaluation,functionTypedEvaluation,argumentTypedEvaluation]
  unfold Active
  split_ifs <;> rfl

theorem activeBranchEvaluation (data : Data) (v : List.Vector Nat 5) :
    evaluate (activeBranch data) v = evaluate (InternalParameterizedCanonicalResultFold.actualJ data)
      (List.Vector.ofFn ![v.get 1,v.get 2,v.get 4,v.get 3,v.get 0]) := by
  change evaluate (InternalParameterizedCanonicalResultFold.actualJ data)
    (List.Vector.ofFn fun i : Fin 5 => evaluate
      ((![Program.projection 1,.projection 2,.projection 4,.projection 3,.projection 0] :
        Fin 5 → Program 5) i) v) = _
  congr 1

/-- Unfold only the outer composition. The actual fold AST is not reduced. -/
theorem applicationEvaluation (data : Data) (d e f a parameter : Nat) :
    evaluate (InternalParameterizedCanonicalResultFold.actualJ data)
      (List.Vector.ofFn ![d,e,f,a,parameter]) =
    evaluate (InternalParameterizedCanonicalResultFold.combine data)
      (List.Vector.ofFn ![d,e,f,
        evaluate (InternalParameterizedCanonicalResultFold.foldN data)
          (List.Vector.ofFn ![a,parameter]),parameter]) :=
  InternalParameterizedCanonicalQuotientEdgeApplicationLiftEvaluationProof.argumentCompositionEvaluation
    (InternalParameterizedCanonicalResultFold.combine data)
    (InternalParameterizedCanonicalResultFold.foldN data) (List.Vector.ofFn ![d,e,f,a,parameter])

/-- Original canonical typed witnesses imply argument fixedness externally.
No fixedness equation or semantic fact is inserted into an internal calculus. -/
theorem activeVertexEquality (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (domain codomain argument value : Nat)
    (hactive : Active data (parameterCode symbols S Gamma table) domain codomain argument value) :
    evaluate (InternalParameterizedCanonicalResultFold.actualJ data)
      (List.Vector.ofFn ![domain,codomain,value,argument,parameterCode symbols S Gamma table]) =
    ApplicationCertificateLiftPath.vertex n arity Gamma
      (OrdinaryArithmeticQuotient.contextCode symbols S table) domain codomain argument value := by
  obtain ⟨hfunction,hargument⟩ := hactive
  obtain ⟨sigma,_,hs⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal domain
  obtain ⟨tau,_,ht⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal codomain
  rw [← hs,← ht] at hfunction ⊢
  rw [← hs] at hargument
  change evaluate (selectedTyped data)
    (List.Vector.ofFn ![value,typeNumber (.arrow sigma tau),parameterCode symbols S Gamma table]) = 1
      at hfunction
  have htyped := InternalOriginalUniformDescentSelectionEvaluationProof.actualOriginalUniformTypedCalibration
    n arity data hc symbols S Gamma table hS
  have hf := (htyped value (typeNumber (.arrow sigma tau))).symm.trans hfunction
  have ha := (htyped argument (typeNumber sigma)).symm.trans hargument
  obtain ⟨⟨fty,f⟩,hfU,hfty,hfx⟩ :=
    InternalCanonicalFixedWindowVertexDispatchEvaluationProof.typedValueWitness
      n arity symbols S Gamma hS (.arrow sigma tau) value hf
  change fty = .arrow sigma tau at hfty
  subst fty
  obtain ⟨⟨aty,a⟩,haU,haty,hay⟩ :=
    InternalCanonicalFixedWindowVertexDispatchEvaluationProof.typedValueWitness
      n arity symbols S Gamma hS sigma argument ha
  change aty = sigma at haty
  subst aty
  obtain ⟨b,hb,hdb,hreb⟩ := NumberedNumericApplicationSupportProof.decodedRepresentative
    n arity symbols S hS Gamma sigma a haU
  have hnb := (NumberedNumericCarrierProof.numericUniverseDecode
    n arity symbols S Gamma _ ⟨sigma,b⟩).mp hdb
  have hr : InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma argument =
      argument := by
    calc
      _ = InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma
          (packedNumber ⟨sigma,b⟩) := by rw [hnb.1,hay]
      _ = representativeCode symbols S ⟨sigma,b⟩ :=
        InternalRepresentativeFoldCalibrationSupportProof.targetOnPacked
          n arity symbols S Gamma ⟨sigma,b⟩
      _ = argument := hreb.trans hay
  have hn := (InternalOriginalUniformCanonicalResultFoldEvaluationProof.actualOriginalUniformCanonicalResultFoldCalibration
    n arity data hc symbols S Gamma table hS argument).1
  rw [hr] at hn
  rw [applicationEvaluation,hn,← hfx,← hay]
  rw [InternalOriginalUniformCanonicalResultFoldSupportProof.typedApplicationCombine
    n arity data hc symbols S hS Gamma table sigma tau f a hfU haU]
  unfold ApplicationCertificateLiftPath.vertex
  rw [OrdinaryArithmeticApplicationSupportProof.concreteCalibration,
    NumberedNumericApplicationProof.canonicalApplicationCalibration
      n arity symbols S hS Gamma sigma tau f a hfU haU]
  rfl

theorem vertexCalibrationAt (n : Nat) (arity : Fin n → Nat) (data : Data) (oldVertex : Program 5)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (hold : OldVertexCalibrated n arity oldVertex)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) :
    VertexCalibratedAt n arity symbols S Gamma table (vertex data oldVertex) := by
  intro d e a x
  rw [vertex,evalBranch,activationEvaluation]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.head_cons,Matrix.tail_cons]
  by_cases ha : Active data (parameterCode symbols S Gamma table) d e a x
  · rw [if_pos ha]
    simp only [Nat.one_ne_zero,if_false]
    rw [activeBranchEvaluation]
    exact activeVertexEquality n arity data hc symbols S Gamma table hS d e a x ha
  · rw [if_neg ha]
    exact oldVertexCalibrationAt n arity oldVertex hold symbols S Gamma table d e a x

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathEvaluationProof
