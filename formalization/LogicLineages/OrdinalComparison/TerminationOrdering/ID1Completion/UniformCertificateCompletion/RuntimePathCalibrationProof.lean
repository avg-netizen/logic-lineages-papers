module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePathCalibrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.DecodedSourceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePathCalibrationProof
open Source NumberedMultisetNumeric NumberedQuotientPathCertificates
open InternalOriginalUniformDescentSelection (Data selectedTyped)
open InternalOriginalUniformParameterLeaves (parameterCode parameterObject)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalApplicationPathMapEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

attribute [local instance] Classical.propDecidable

/-- Literal outer context extraction; the raw context is not re-encoded. -/
theorem windowAtEvaluation (window : Program 1) (v : List.Vector Nat 5) :
    evaluate (Path.windowAt window) v =
      evaluate window (ofFn ![(Nat.unpair (v.get 0)).1]) := by
  change evaluate window (ofFn fun _ : Fin 1 => evaluate (leftOf (.projection 0)) v) = _
  rw [leftOfEvaluation]
  rfl

theorem functionTypedEvaluation (data : Data) (v : List.Vector Nat 5) :
    evaluate (Path.functionTyped data) v = evaluate (selectedTyped data)
      (ofFn ![v.get 4,1 + Nat.pair (v.get 1) (v.get 2),v.get 0]) :=
  InternalOriginalUniformVertexPathEvaluationProof.functionTypedEvaluation data v

theorem argumentTypedEvaluation (data : Data) (v : List.Vector Nat 5) :
    evaluate (Path.argumentTyped data) v = evaluate (selectedTyped data)
      (ofFn ![v.get 3,v.get 1,v.get 0]) :=
  InternalOriginalUniformVertexPathEvaluationProof.argumentTypedEvaluation data v

theorem activationEvaluation (data : Data) (window : Program 1) (v : List.Vector Nat 5) :
    evaluate (Path.activation data window) v =
      if evaluate window (ofFn ![(Nat.unpair (v.get 0)).1]) = 1 ∧
        InternalOriginalUniformVertexPath.Active data
          (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4)
      then 1 else 0 := by
  rw [Path.activation,conjunctionEvaluation,windowAtEvaluation,conjunctionEvaluation,
    functionTypedEvaluation,argumentTypedEvaluation]
  unfold InternalOriginalUniformVertexPath.Active
  by_cases hw : evaluate window (ofFn ![(Nat.unpair (v.get 0)).1]) = 1 <;>
    by_cases hf : evaluate (selectedTyped data)
      (ofFn ![v.get 4,1 + Nat.pair (v.get 1) (v.get 2),v.get 0]) = 1 <;>
    by_cases ha : evaluate (selectedTyped data) (ofFn ![v.get 3,v.get 1,v.get 0]) = 1 <;>
    simp only [hw,hf,ha,if_true,if_false,and_true,and_false,and_self,Nat.zero_ne_one]

theorem activeBranchEvaluation (data : Data) (v : List.Vector Nat 5) :
    evaluate (Path.activeBranch data) v =
      evaluate (InternalParameterizedCanonicalResultFold.actualJ data)
        (ofFn ![v.get 1,v.get 2,v.get 4,v.get 3,v.get 0]) :=
  InternalOriginalUniformVertexPathEvaluationProof.activeBranchEvaluation data v

/-- Transfer the already checked ORIGINAL canonical active-vertex theorem
along the actual decoded slices. Only equality of decoder results is used
on the semantic side; no raw Context encode/decode converse is asserted. -/
theorem activeVertexAt (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (parameter : Nat) (ctx : OrdinaryArithmeticQuotient.Context n)
    (hctx : Encodable.decode (Nat.unpair parameter).1 = some ctx)
    (hS : SubtypeClosed (fun typ => typ ∈ ctx.1.2)) (Gamma : List Ty)
    (ho : ∀ value : Nat, parameterObject value parameter = some (Gamma,value))
    (domain codomain argument value : Nat)
    (ha : InternalOriginalUniformVertexPath.Active data parameter domain codomain argument value) :
    evaluate (InternalParameterizedCanonicalResultFold.actualJ data)
        (ofFn ![domain,codomain,value,argument,parameter]) =
      ApplicationCertificateLiftPath.vertex n arity Gamma (Nat.unpair parameter).1
        domain codomain argument value := by
  have hs := ParameterSliceProof.actualOriginalCompositeParameterSliceCongruence data parameter
    (parameterCode ctx.1.1 ctx.1.2 Gamma ctx.2)
    (DecodedSourceCalibrationProof.decodedAtomic n arity data hc parameter ctx hctx Gamma ho)
  have hcanonical : InternalOriginalUniformVertexPath.Active data
      (parameterCode ctx.1.1 ctx.1.2 Gamma ctx.2) domain codomain argument value :=
    ⟨(hs.typed value (1 + Nat.pair domain codomain)).symm.trans ha.1,
      (hs.typed argument domain).symm.trans ha.2⟩
  calc
    _ = evaluate (InternalParameterizedCanonicalResultFold.actualJ data)
        (ofFn ![domain,codomain,value,argument,parameterCode ctx.1.1 ctx.1.2 Gamma ctx.2]) :=
      hs.application domain codomain value argument
    _ = ApplicationCertificateLiftPath.vertex n arity Gamma
        (OrdinaryArithmeticQuotient.contextCode ctx.1.1 ctx.1.2 ctx.2)
        domain codomain argument value :=
      InternalOriginalUniformVertexPathEvaluationProof.activeVertexEquality
        n arity data hc ctx.1.1 ctx.1.2 Gamma ctx.2 hS domain codomain argument value hcanonical
    _ = _ := by
      simp only [ApplicationCertificateLiftPath.vertex,OrdinaryArithmeticApplication.decodedApplication,
        OrdinaryArithmeticQuotient.contextCode,Encodable.encodek,hctx]

/-- R006 semantics at the SAME actual runtime Gamma. The full original raw
vertex remains present, including every original decoding/default branch. -/
theorem runtimeValueAt (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 5)
    (Gamma : List Ty)
    (ho : ∀ value : Nat, parameterObject value (v.get 0) = some (Gamma,value)) :
    RuntimeVertex.value n arity v =
      ApplicationCertificateLiftPath.vertex n arity Gamma (Nat.unpair (v.get 0)).1
        (v.get 1) (v.get 2) (v.get 3) (v.get 4) := by
  unfold RuntimeVertex.value
  rw [ho 0]
  rfl

/-- All-input calibration of the literal global-window dispatcher. An
inactive input keeps the entire fallback, not a freshly paired zero. -/
theorem vertexCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (window : Program 1) (oldVertex : Program 5)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (hw : Path.windowCalibrated n window)
    (hold : ∀ v : List.Vector Nat 5, evaluate oldVertex v = RuntimeVertex.value n arity v)
    (v : List.Vector Nat 5) :
    evaluate (Path.vertex data window oldVertex) v = RuntimeVertex.value n arity v := by
  rw [Path.vertex,evalBranch,activationEvaluation]
  by_cases ha : evaluate window (ofFn ![(Nat.unpair (v.get 0)).1]) = 1 ∧
      InternalOriginalUniformVertexPath.Active data
        (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4)
  · rw [if_pos ha]
    simp only [Nat.one_ne_zero,if_false]
    have hwin : GuardCalibration.validWindow n (Nat.unpair (v.get 0)).1 = 1 :=
      (hw (ofFn ![(Nat.unpair (v.get 0)).1])).symm.trans ha.1
    obtain ⟨ctx,hctx,hS⟩ :=
      (GuardCalibrationProof.actualValidWindowCalibration n (Nat.unpair (v.get 0)).1).1.mp hwin
    obtain ⟨Gamma,ho⟩ :=
      SourceComputabilityCompletion.BottomRepresentativeEvaluationProof.parameterGamma (v.get 0)
    rw [activeBranchEvaluation,runtimeValueAt n arity v Gamma ho]
    exact activeVertexAt n arity data hc (v.get 0) ctx hctx hS Gamma ho
      (v.get 1) (v.get 2) (v.get 3) (v.get 4) ha.2
  · rw [if_neg ha]
    exact hold v

/-- Original pair entries and edge certificates at a fixed arbitrary p.
Only the corresponding vertex slice is needed, not a fixed-Gamma global
program contract with p misidentified as the original raw context. -/
theorem entryCalibrationAt (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (vertexProgram : Program 5) (parameter : Nat)
    (hv : ∀ domain codomain argument value : Nat,
      evaluate vertexProgram (ofFn ![parameter,domain,codomain,argument,value]) =
        ApplicationCertificateLiftPath.vertex n arity Gamma (Nat.unpair parameter).1
          domain codomain argument value)
    (domain codomain argument raw : Nat) :
    evaluate (InternalApplicationPathMap.entry vertexProgram)
        (raw ::ᵥ ofFn ![parameter,domain,codomain,argument]) =
      Nat.pair (ApplicationCertificateLiftPath.vertex n arity Gamma (Nat.unpair parameter).1
          domain codomain argument (Nat.unpair raw).1)
        (ApplicationCertificateLiftEdge.liftEdge domain codomain argument (Nat.unpair raw).2) := by
  rw [InternalApplicationPathMap.entry,pairOfEvaluation,entryVertexEvaluation,entryEdgeEvaluation]
  change Nat.pair (evaluate vertexProgram
      (ofFn ![parameter,domain,codomain,argument,(Nat.unpair raw).1]))
    (ApplicationCertificateLiftEdge.liftEdge domain codomain argument (Nat.unpair raw).2) = _
  rw [hv]

/-- Original raw-list map evaluation and total original path decoding cover
EVERY certificate code, without path acceptance or endpoint restrictions. -/
theorem mapCalibrationAt (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (vertexProgram : Program 5) (parameter : Nat)
    (hv : ∀ domain codomain argument value : Nat,
      evaluate vertexProgram (ofFn ![parameter,domain,codomain,argument,value]) =
        ApplicationCertificateLiftPath.vertex n arity Gamma (Nat.unpair parameter).1
          domain codomain argument value)
    (domain codomain argument code : Nat) :
    evaluate (InternalApplicationPathMap.pathMap vertexProgram)
        (ofFn ![code,parameter,domain,codomain,argument]) =
      ApplicationCertificateLiftPath.liftPath n arity Gamma (Nat.unpair parameter).1
        domain codomain argument code := by
  let params : List.Vector Nat 4 := ofFn ![parameter,domain,codomain,argument]
  have inputs : ofFn ![code,parameter,domain,codomain,argument] = code ::ᵥ params := by
    apply List.Vector.ext
    intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (fun q => Fin.elim0 q))))) i
  rw [inputs,InternalApplicationPathMap.pathMap,InternalListMapEvaluationProof.actualRawListMapEvaluation]
  obtain ⟨entries,hentries⟩ := NumberedQuotientPathNumericTotalityProof.decoderTotality code
  have hnumber := (NumberedQuotientPathNumericTotalityProof.actualPathDecoderEquation code entries).mp hentries
  have hn : decodeNumbers code = some (entries.map (fun entry => Nat.pair entry.1 entry.2)) := by
    rw [← hnumber]
    exact NumberedMultisetNumericSupportProof.numbersRoundTrip _
  rw [ApplicationCertificateLiftPath.liftPath,hentries,hn]
  simp only [Option.getD_some,pathCertificateNumber,ApplicationCertificateLiftPath.liftEntries,
    List.map_map,Function.comp_def]
  apply congrArg numbersNumber
  apply congrArg (fun f : EdgeEntry → Nat => entries.map f)
  funext entry
  simpa only [Nat.unpair_pair] using
    entryCalibrationAt n arity Gamma vertexProgram parameter hv domain codomain argument
      (Nat.pair entry.1 entry.2)

/-- The original three program choices are fixed before every raw window,
parameter and payload; one Gamma per p serves both vertex and mapper. -/
theorem actualOriginalRuntimePathCalibration :
    RuntimePathCalibrationTargets.ActualOriginalRuntimePathCalibration := by
  intro n arity data window oldVertex hc hw hold
  have hv := vertexCalibration n arity data window oldVertex hc hw hold
  refine ⟨hv,?_⟩
  intro parameter
  obtain ⟨Gamma,ho⟩ :=
    SourceComputabilityCompletion.BottomRepresentativeEvaluationProof.parameterGamma parameter
  have hs : ∀ domain codomain argument value : Nat,
      evaluate (Path.vertex data window oldVertex) (ofFn ![parameter,domain,codomain,argument,value]) =
        ApplicationCertificateLiftPath.vertex n arity Gamma (Nat.unpair parameter).1
          domain codomain argument value := by
    intro domain codomain argument value
    rw [hv]
    exact runtimeValueAt n arity (ofFn ![parameter,domain,codomain,argument,value]) Gamma ho
  exact ⟨Gamma,ho,hs,mapCalibrationAt n arity Gamma (Path.vertex data window oldVertex) parameter hs⟩

theorem actualOriginalRuntimeVertexFallback :
    RuntimePathCalibrationTargets.ActualOriginalRuntimeVertexFallback := by
  intro data window oldVertex v h
  change evaluate (Path.vertex data window oldVertex) v = _
  rw [Path.vertex,evalBranch,h]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePathCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePathCalibrationProof
