module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathPrimitiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathNumericTotalityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapEvaluationProof
open Source NumberedMultisetNumeric NumberedQuotientPathCertificates
open InternalApplicationPathMap InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

attribute [local irreducible] Primrec
attribute [local irreducible] ApplicationCertificateLiftPath.vertex

theorem vertexPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun v : List.Vector Nat 5 => ApplicationCertificateLiftPath.vertex n arity Gamma
      (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4)) := by
  have getP (i : Fin 5) : Primrec (fun v : List.Vector Nat 5 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hp : Primrec (fun v : List.Vector Nat 5 =>
      ((Gamma,v.get 0,v.get 1,v.get 2,v.get 3),v.get 4)) :=
    (((Primrec.const Gamma).pair
      ((getP 0).pair ((getP 1).pair ((getP 2).pair (getP 3))))).pair (getP 4))
  exact (ApplicationCertificateLiftPathPrimitiveProof.vertexPrimitive n arity).comp hp

theorem actualOriginalVertexProgramExists :
    InternalApplicationPathMapTargets.ActualOriginalVertexProgramExists := by
  intro n arity Gamma
  exact Proof.allPrimitiveFunctions 5
    (fun v : List.Vector Nat 5 => ApplicationCertificateLiftPath.vertex n arity Gamma
      (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4))
    (vertexPrimitive n arity Gamma)

theorem entryVertexEvaluation (vertexProgram : Program 5) (v : List.Vector Nat 5) :
    evaluate (entryVertex vertexProgram) v = evaluate vertexProgram
      (List.Vector.ofFn ![v.get 1,v.get 2,v.get 3,v.get 4,(Nat.unpair (v.get 0)).1]) := by
  change evaluate vertexProgram (List.Vector.ofFn fun i : Fin 5 =>
    evaluate ((![Program.projection 1,.projection 2,.projection 3,.projection 4,
      leftOf (.projection 0)] : Fin 5 → Program 5) i) v) = _
  congr 1
  apply List.Vector.ext
  intro i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases (leftOfEvaluation (.projection 0) v) (fun q => Fin.elim0 q))))) i

theorem entryEdgeEvaluation (v : List.Vector Nat 5) :
    evaluate entryEdge v = ApplicationCertificateLiftEdge.liftEdge
      (v.get 2) (v.get 3) (v.get 4) (Nat.unpair (v.get 0)).2 := by
  change evaluate InternalApplicationCertificateConstructors.edgeLift
    (List.Vector.ofFn fun i : Fin 4 =>
      evaluate ((![Program.projection 2,.projection 3,.projection 4,
        rightOf (.projection 0)] : Fin 4 → Program 5) i) v) = _
  rw [edgeLiftEvaluation]
  change ApplicationCertificateLiftEdge.liftEdge (v.get 2) (v.get 3) (v.get 4)
    (evaluate (rightOf (.projection 0)) v) = _
  rw [rightOfEvaluation]
  rfl

theorem actualOriginalEntryCalibration :
    InternalApplicationPathMapTargets.ActualOriginalEntryCalibration := by
  intro n arity Gamma vertexProgram hvertex v
  rw [entry,pairOfEvaluation,entryVertexEvaluation,entryEdgeEvaluation,hvertex]
  rfl

theorem pathEvaluationCons (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (vertexProgram : Program 5) (hvertex : VertexCalibrated n arity Gamma vertexProgram)
    (params : List.Vector Nat 4) (code : Nat) :
    evaluate (pathMap vertexProgram) (code ::ᵥ params) =
      ApplicationCertificateLiftPath.liftPath n arity Gamma
        (params.get 0) (params.get 1) (params.get 2) (params.get 3) code := by
  rw [pathMap,InternalListMapEvaluationProof.actualRawListMapEvaluation]
  obtain ⟨entries, hentries⟩ := NumberedQuotientPathNumericTotalityProof.decoderTotality code
  have hnumber := (NumberedQuotientPathNumericTotalityProof.actualPathDecoderEquation code entries).mp hentries
  have hn : decodeNumbers code = some (entries.map (fun e => Nat.pair e.1 e.2)) := by
    rw [← hnumber]
    exact NumberedMultisetNumericSupportProof.numbersRoundTrip _
  rw [ApplicationCertificateLiftPath.liftPath,hentries,hn]
  simp only [Option.getD_some,pathCertificateNumber,ApplicationCertificateLiftPath.liftEntries,
    List.map_map,Function.comp_def]
  apply congrArg numbersNumber
  apply congrArg (fun f : EdgeEntry → Nat => entries.map f)
  funext e
  have h1 : (Nat.pair e.1 e.2 ::ᵥ params).get 1 = params.get 0 :=
    List.Vector.get_cons_succ _ params 0
  have h2 : (Nat.pair e.1 e.2 ::ᵥ params).get 2 = params.get 1 :=
    List.Vector.get_cons_succ _ params 1
  have h3 : (Nat.pair e.1 e.2 ::ᵥ params).get 3 = params.get 2 :=
    List.Vector.get_cons_succ _ params 2
  have h4 : (Nat.pair e.1 e.2 ::ᵥ params).get 4 = params.get 3 :=
    List.Vector.get_cons_succ _ params 3
  simpa only [List.Vector.get_cons_zero,h1,h2,h3,h4,Nat.unpair_pair] using
    actualOriginalEntryCalibration n arity Gamma vertexProgram hvertex
      (Nat.pair e.1 e.2 ::ᵥ params)

theorem actualOriginalPathCalibration :
    InternalApplicationPathMapTargets.ActualOriginalPathCalibration := by
  intro n arity Gamma vertexProgram hvertex v
  let params : List.Vector Nat 4 := List.Vector.ofFn ![v.get 1,v.get 2,v.get 3,v.get 4]
  have hv : v.get 0 ::ᵥ params = v := by
    apply List.Vector.ext
    intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (fun q => Fin.elim0 q))))) i
  have h := pathEvaluationCons n arity Gamma vertexProgram hvertex params (v.get 0)
  rw [hv] at h
  exact h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationPathMapEvaluationProof
