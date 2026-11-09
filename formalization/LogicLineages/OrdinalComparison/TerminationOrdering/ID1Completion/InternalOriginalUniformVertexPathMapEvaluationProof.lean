module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathMapEvaluationProof
open Source NumberedMultisetNumeric NumberedQuotientPathCertificates
open InternalOriginalUniformVertexPath InternalOriginalUniformVertexPathTargets
open InternalOriginalUniformVertexPathEvaluationProof
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformParameterLeaves (parameterCode)
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationPathMapEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- Original pair entries and edge certificates retain all raw coordinates.
Only the fixed parameter slice of the supplied vertex is needed. -/
theorem entryCalibrationAt (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (vertexProgram : Program 5)
    (hv : VertexCalibratedAt n arity symbols S Gamma table vertexProgram)
    (d e a raw : Nat) :
    evaluate (InternalApplicationPathMap.entry vertexProgram)
      (raw ::ᵥ List.Vector.ofFn ![parameterCode symbols S Gamma table,d,e,a]) =
    Nat.pair (ApplicationCertificateLiftPath.vertex n arity Gamma
      (OrdinaryArithmeticQuotient.contextCode symbols S table) d e a (Nat.unpair raw).1)
      (ApplicationCertificateLiftEdge.liftEdge d e a (Nat.unpair raw).2) := by
  rw [InternalApplicationPathMap.entry,pairOfEvaluation,entryVertexEvaluation,entryEdgeEvaluation]
  change Nat.pair (evaluate vertexProgram
      (List.Vector.ofFn ![parameterCode symbols S Gamma table,d,e,a,(Nat.unpair raw).1]))
    (ApplicationCertificateLiftEdge.liftEdge d e a (Nat.unpair raw).2) = _
  rw [hv]

/-- The original raw-list map theorem covers every numeric code. Original
decoder totality identifies the exact original entry list before mapping. -/
theorem mapCalibrationAt (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (vertexProgram : Program 5)
    (hv : VertexCalibratedAt n arity symbols S Gamma table vertexProgram) :
    MapCalibratedAt n arity symbols S Gamma table vertexProgram := by
  intro d e a code
  let params : List.Vector Nat 4 := List.Vector.ofFn ![parameterCode symbols S Gamma table,d,e,a]
  have inputs : List.Vector.ofFn ![code,parameterCode symbols S Gamma table,d,e,a] =
      code ::ᵥ params := by
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
    entryCalibrationAt n arity symbols S Gamma table vertexProgram hv d e a (Nat.pair entry.1 entry.2)

theorem actualOriginalUniformVertexPathCalibration : ActualOriginalUniformVertexPathCalibration := by
  intro n arity data oldVertex hc hold symbols S Gamma table hS
  have hv := vertexCalibrationAt n arity data oldVertex hc hold symbols S Gamma table hS
  exact ⟨hv,mapCalibrationAt n arity symbols S Gamma table (vertex data oldVertex) hv⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathMapEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathMapEvaluationProof
