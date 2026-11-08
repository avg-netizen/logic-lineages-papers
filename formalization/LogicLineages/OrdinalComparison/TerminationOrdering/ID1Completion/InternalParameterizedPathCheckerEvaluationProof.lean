module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathNumericTotalityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerEvaluationProof
open Source NumberedMultisetNumeric NumberedQuotientPathCertificates
open InternalParameterizedPathChecker InternalListCodec
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo vectorThree exactEqualityEvaluation)
open InternalListCodecEvaluationProof (consEvaluation headEvaluation tailEvaluation)
open InternalUnpairEvaluationProof (exactUnpairEvaluation)
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open InternalRawListRecursionEvaluationProof (actualRawListRecursionEvaluation)

attribute [local irreducible] consCode headCode tailCode InternalUnpair.left InternalUnpair.right
  InternalEqualityTest.equalityTest

theorem vectorFour (f : Fin 4 → Nat) :
    List.Vector.ofFn f = f 0 ::ᵥ f 1 ::ᵥ f 2 ::ᵥ f 3 ::ᵥ List.Vector.nil := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => ?_) k) j) i
  · simp <;> rfl
  · simp <;> rfl
  · simp <;> rfl
  · obtain rfl : l = 0 := Fin.eq_zero l
    simp <;> rfl

theorem summaryHeadEvaluation (x y state parameter : Nat) :
    evaluate summaryHead (x ::ᵥ y ::ᵥ state ::ᵥ parameter ::ᵥ List.Vector.nil) =
      (Nat.unpair (state - 1)).1 := by
  change evaluate headCode (List.Vector.ofFn fun _ : Fin 1 => state) = _
  rw [vectorOne,headEvaluation]

theorem summaryVertexEvaluation (x y state parameter : Nat) :
    evaluate summaryVertex (x ::ᵥ y ::ᵥ state ::ᵥ parameter ::ᵥ List.Vector.nil) =
      (Nat.unpair (Nat.unpair (state - 1)).1).1 := by
  change evaluate InternalUnpair.left (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate summaryHead (x ::ᵥ y ::ᵥ state ::ᵥ parameter ::ᵥ List.Vector.nil)) = _
  rw [vectorOne,(exactUnpairEvaluation _).1,summaryHeadEvaluation]

theorem summaryCertificateEvaluation (x y state parameter : Nat) :
    evaluate summaryCertificate (x ::ᵥ y ::ᵥ state ::ᵥ parameter ::ᵥ List.Vector.nil) =
      (Nat.unpair (Nat.unpair (state - 1)).1).2 := by
  change evaluate InternalUnpair.right (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate summaryHead (x ::ᵥ y ::ᵥ state ::ᵥ parameter ::ᵥ List.Vector.nil)) = _
  rw [vectorOne,(exactUnpairEvaluation _).2,summaryHeadEvaluation]

theorem summaryTailEvaluation (x y state parameter : Nat) :
    evaluate summaryTail (x ::ᵥ y ::ᵥ state ::ᵥ parameter ::ᵥ List.Vector.nil) =
      (Nat.unpair (state - 1)).2 := by
  change evaluate tailCode (List.Vector.ofFn fun _ : Fin 1 => state) = _
  rw [vectorOne,tailEvaluation]

theorem endpointsEqualEvaluation (x y state parameter : Nat) :
    evaluate endpointsEqual (x ::ᵥ y ::ᵥ state ::ᵥ parameter ::ᵥ List.Vector.nil) =
      if x = y then 1 else 0 := by
  change evaluate InternalEqualityTest.equalityTest (List.Vector.ofFn fun i : Fin 2 =>
    evaluate ((Fin.cons (Program.projection 0)
      (Fin.cons (Program.projection 1) Fin.elim0) : Fin 2 → Program 4) i)
      (x ::ᵥ y ::ᵥ state ::ᵥ parameter ::ᵥ List.Vector.nil)) = _
  rw [vectorTwo]
  exact exactEqualityEvaluation x y

theorem edgeAtSummaryEvaluation (edge : Program 4) (x y state parameter : Nat) :
    evaluate (edgeAtSummary edge) (x ::ᵥ y ::ᵥ state ::ᵥ parameter ::ᵥ List.Vector.nil) =
      evaluate edge (x ::ᵥ (Nat.unpair (Nat.unpair (state - 1)).1).1 ::ᵥ
        (Nat.unpair (Nat.unpair (state - 1)).1).2 ::ᵥ parameter ::ᵥ List.Vector.nil) := by
  change evaluate edge (List.Vector.ofFn fun i : Fin 4 =>
    evaluate ((quadruple (Program.projection 0) summaryVertex summaryCertificate (Program.projection 3) :
      Fin 4 → Program 4) i) (x ::ᵥ y ::ᵥ state ::ᵥ parameter ::ᵥ List.Vector.nil)) = _
  rw [vectorFour]
  change evaluate edge (x ::ᵥ
    evaluate summaryVertex (x ::ᵥ y ::ᵥ state ::ᵥ parameter ::ᵥ List.Vector.nil) ::ᵥ
    evaluate summaryCertificate (x ::ᵥ y ::ᵥ state ::ᵥ parameter ::ᵥ List.Vector.nil) ::ᵥ parameter ::ᵥ List.Vector.nil) = _
  rw [summaryVertexEvaluation,summaryCertificateEvaluation]

/-- The empty suffix implements the original two distinct stopping rules. -/
theorem finishZeroEvaluation (edge : Program 4) (positive : Bool) (x y parameter : Nat) :
    evaluate (finish edge positive) (x ::ᵥ y ::ᵥ 0 ::ᵥ parameter ::ᵥ List.Vector.nil) =
      if positive then 0 else if x = y then 1 else 0 := by
  rw [finish,evalBranch]
  change (if (0 : Nat) = 0 then
    evaluate (emptyFinish positive) (x ::ᵥ y ::ᵥ 0 ::ᵥ parameter ::ᵥ List.Vector.nil) else _) = _
  rw [if_pos rfl]
  cases positive with
  | false => exact endpointsEqualEvaluation x y 0 parameter
  | true => rfl

/-- A nonempty summary tests its pending edge and the exact suffix value. -/
theorem finishConsEvaluation (edge : Program 4) (positive : Bool)
    (x y raw suffix parameter : Nat) :
    evaluate (finish edge positive)
      (x ::ᵥ y ::ᵥ (1 + Nat.pair raw suffix) ::ᵥ parameter ::ᵥ List.Vector.nil) =
      if evaluate edge (x ::ᵥ (Nat.unpair raw).1 ::ᵥ
          (Nat.unpair raw).2 ::ᵥ parameter ::ᵥ List.Vector.nil) = 1 ∧ suffix = 1 then 1 else 0 := by
  rw [finish,evalBranch]
  change (if 1 + Nat.pair raw suffix = 0 then _ else
    evaluate (nonemptyFinish edge)
      (x ::ᵥ y ::ᵥ (1 + Nat.pair raw suffix) ::ᵥ parameter ::ᵥ List.Vector.nil)) = _
  have hn : 1 + Nat.pair raw suffix ≠ 0 := by omega
  rw [if_neg hn,nonemptyFinish,actualConjunctionEvaluation,
    edgeAtSummaryEvaluation,summaryTailEvaluation]
  simp [Nat.add_comm 1]

theorem entryVertexEvaluation (raw state target parameter : Nat) :
    evaluate entryVertex (raw ::ᵥ state ::ᵥ target ::ᵥ parameter ::ᵥ List.Vector.nil) =
      (Nat.unpair raw).1 := by
  change evaluate InternalUnpair.left (List.Vector.ofFn fun _ : Fin 1 => raw) = _
  rw [vectorOne]
  exact (exactUnpairEvaluation raw).1

theorem tailRunEvaluation (edge : Program 4) (raw state target parameter : Nat) :
    evaluate (tailRun edge) (raw ::ᵥ state ::ᵥ target ::ᵥ parameter ::ᵥ List.Vector.nil) =
      evaluate (finish edge false)
        ((Nat.unpair raw).1 ::ᵥ target ::ᵥ state ::ᵥ parameter ::ᵥ List.Vector.nil) := by
  change evaluate (finish edge false) (List.Vector.ofFn fun i : Fin 4 =>
    evaluate ((quadruple entryVertex (Program.projection 2) (Program.projection 1) (Program.projection 3) :
      Fin 4 → Program 4) i) (raw ::ᵥ state ::ᵥ target ::ᵥ parameter ::ᵥ List.Vector.nil)) = _
  rw [vectorFour]
  change evaluate (finish edge false)
    (evaluate entryVertex (raw ::ᵥ state ::ᵥ target ::ᵥ parameter ::ᵥ List.Vector.nil) ::ᵥ
      target ::ᵥ state ::ᵥ parameter ::ᵥ List.Vector.nil) = _
  rw [entryVertexEvaluation]

theorem summaryStepEvaluation (edge : Program 4) (raw state target parameter : Nat) :
    evaluate (summaryStep edge) (raw ::ᵥ state ::ᵥ target ::ᵥ parameter ::ᵥ List.Vector.nil) =
      1 + Nat.pair raw (evaluate (finish edge false)
        ((Nat.unpair raw).1 ::ᵥ target ::ᵥ state ::ᵥ parameter ::ᵥ List.Vector.nil)) := by
  change evaluate consCode (List.Vector.ofFn fun i : Fin 2 =>
    evaluate ((Fin.cons (Program.projection 0) (Fin.cons (tailRun edge) Fin.elim0) :
      Fin 2 → Program 4) i) (raw ::ᵥ state ::ᵥ target ::ᵥ parameter ::ᵥ List.Vector.nil)) = _
  rw [vectorTwo,consEvaluation]
  change 1 + Nat.pair raw
    (evaluate (tailRun edge) (raw ::ᵥ state ::ᵥ target ::ᵥ parameter ::ᵥ List.Vector.nil)) = _
  rw [tailRunEvaluation]

/-- A proof-side name for the actual raw-list fold on original paired entries. -/
def foldedSummary (edge : Program 4) (target parameter : Nat) (entries : List EdgeEntry) : Nat :=
  (entries.map (fun e => Nat.pair e.1 e.2)).foldr
    (fun raw state => evaluate (summaryStep edge)
      (raw ::ᵥ state ::ᵥ target ::ᵥ parameter ::ᵥ List.Vector.nil)) 0

theorem foldedSummaryNil (edge : Program 4) (target parameter : Nat) :
    foldedSummary edge target parameter [] = 0 := rfl

theorem foldedSummaryCons (edge : Program 4) (target parameter vertex certificate : Nat)
    (entries : List EdgeEntry) :
    foldedSummary edge target parameter ((vertex,certificate) :: entries) =
      1 + Nat.pair (Nat.pair vertex certificate)
        (evaluate (finish edge false)
          (vertex ::ᵥ target ::ᵥ foldedSummary edge target parameter entries ::ᵥ parameter ::ᵥ List.Vector.nil)) := by
  change evaluate (summaryStep edge)
    (Nat.pair vertex certificate ::ᵥ foldedSummary edge target parameter entries ::ᵥ target ::ᵥ parameter ::ᵥ List.Vector.nil) = _
  rw [summaryStepEvaluation,Nat.unpair_pair]

theorem finishFoldEvaluation (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (edge : Program 4) (parameter : Nat)
    (hedge : EdgeCalibrated n arity symbols S Gamma table edge parameter)
    (x y : Nat) (entries : List EdgeEntry) :
    evaluate (finish edge false)
      (x ::ᵥ y ::ᵥ foldedSummary edge y parameter entries ::ᵥ parameter ::ᵥ List.Vector.nil) =
      if pathTest n arity symbols S Gamma table x y entries then 1 else 0 := by
  induction entries generalizing x with
  | nil =>
    rw [foldedSummaryNil,finishZeroEvaluation]
    simp [pathTest]
  | cons entry entries ih =>
    obtain ⟨vertex,certificate⟩ := entry
    rw [foldedSummaryCons,finishConsEvaluation,Nat.unpair_pair,
      hedge x vertex certificate,ih vertex]
    cases he : NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table x vertex certificate <;>
      cases ht : pathTest n arity symbols S Gamma table vertex y entries <;>
      simp [pathTest,he,ht]

/-- The original first entry is retained literally; its tail field is exactly
the acceptance value of the remaining original path from that entry's vertex. -/
theorem summaryFoldInvariant (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (edge : Program 4) (parameter : Nat)
    (hedge : EdgeCalibrated n arity symbols S Gamma table edge parameter)
    (y : Nat) (entries : List EdgeEntry) :
    foldedSummary edge y parameter entries =
      match entries with
      | [] => 0
      | (vertex,certificate) :: rest =>
        1 + Nat.pair (Nat.pair vertex certificate)
          (if pathTest n arity symbols S Gamma table vertex y rest then 1 else 0) := by
  cases entries with
  | nil => rfl
  | cons entry entries =>
    obtain ⟨vertex,certificate⟩ := entry
    rw [foldedSummaryCons,finishFoldEvaluation n arity symbols S Gamma table edge parameter hedge]

theorem positiveFinishFoldEvaluation (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (edge : Program 4) (parameter : Nat)
    (hedge : EdgeCalibrated n arity symbols S Gamma table edge parameter)
    (x y : Nat) (entries : List EdgeEntry) :
    evaluate (finish edge true)
      (x ::ᵥ y ::ᵥ foldedSummary edge y parameter entries ::ᵥ parameter ::ᵥ List.Vector.nil) =
      match entries with
      | [] => 0
      | _ :: _ => if pathTest n arity symbols S Gamma table x y entries then 1 else 0 := by
  cases entries with
  | nil => rw [foldedSummaryNil,finishZeroEvaluation]; rfl
  | cons entry entries =>
    obtain ⟨vertex,certificate⟩ := entry
    have h := finishFoldEvaluation n arity symbols S Gamma table edge parameter hedge x y
      ((vertex,certificate) :: entries)
    rw [foldedSummaryCons,finishConsEvaluation] at h
    rw [foldedSummaryCons,finishConsEvaluation]
    exact h

theorem summaryDecodedEvaluation (edge : Program 4) (target code parameter : Nat)
    (entries : List EdgeEntry) (hdecode : decodePathCertificate code = some entries) :
    evaluate (summary edge) (code ::ᵥ target ::ᵥ parameter ::ᵥ List.Vector.nil) =
      foldedSummary edge target parameter entries := by
  have hnumber :=
    (NumberedQuotientPathNumericTotalityProof.actualPathDecoderEquation code entries).mp hdecode
  have hraw : decodeNumbers code = some (entries.map (fun e => Nat.pair e.1 e.2)) := by
    rw [← hnumber]
    exact NumberedMultisetNumericSupportProof.numbersRoundTrip _
  rw [summary,actualRawListRecursionEvaluation,hraw]
  rfl

theorem summaryAtEvaluation (edge : Program 4) (x y code parameter : Nat) :
    evaluate (summaryAt edge) (x ::ᵥ y ::ᵥ code ::ᵥ parameter ::ᵥ List.Vector.nil) =
      evaluate (summary edge) (code ::ᵥ y ::ᵥ parameter ::ᵥ List.Vector.nil) := by
  change evaluate (summary edge) (List.Vector.ofFn fun i : Fin 3 =>
    evaluate ((InternalPathChecker.triple (Program.projection 2) (Program.projection 1) (Program.projection 3) :
      Fin 3 → Program 4) i) (x ::ᵥ y ::ᵥ code ::ᵥ parameter ::ᵥ List.Vector.nil)) = _
  rw [vectorThree]
  rfl

theorem checkerEvaluation (edge : Program 4) (positive : Bool) (x y code parameter : Nat) :
    evaluate (checker edge positive) (x ::ᵥ y ::ᵥ code ::ᵥ parameter ::ᵥ List.Vector.nil) =
      evaluate (finish edge positive)
        (x ::ᵥ y ::ᵥ evaluate (summary edge) (code ::ᵥ y ::ᵥ parameter ::ᵥ List.Vector.nil) ::ᵥ parameter ::ᵥ List.Vector.nil) := by
  change evaluate (finish edge positive) (List.Vector.ofFn fun i : Fin 4 =>
    evaluate ((quadruple (Program.projection 0) (Program.projection 1) (summaryAt edge) (Program.projection 3) :
      Fin 4 → Program 4) i) (x ::ᵥ y ::ᵥ code ::ᵥ parameter ::ᵥ List.Vector.nil)) = _
  rw [vectorFour]
  change evaluate (finish edge positive)
    (x ::ᵥ y ::ᵥ evaluate (summaryAt edge) (x ::ᵥ y ::ᵥ code ::ᵥ parameter ::ᵥ List.Vector.nil) ::ᵥ parameter ::ᵥ List.Vector.nil) = _
  rw [summaryAtEvaluation]

theorem actualOriginalParameterizedPathCheckerEvaluation :
    InternalParameterizedPathCheckerTargets.ActualOriginalParameterizedPathCheckerEvaluation := by
  intro n arity symbols S Gamma table edge parameter hedge x y code
  obtain ⟨entries,hentries⟩ := NumberedQuotientPathNumericTotalityProof.decoderTotality code
  rw [checkerEvaluation,summaryDecodedEvaluation edge y code parameter entries hentries,hentries]
  exact finishFoldEvaluation n arity symbols S Gamma table edge parameter hedge x y entries

theorem actualOriginalParameterizedPositivePathCheckerEvaluation :
    InternalParameterizedPathCheckerTargets.ActualOriginalParameterizedPositivePathCheckerEvaluation := by
  intro n arity symbols S Gamma table edge parameter hedge x y code
  obtain ⟨entries,hentries⟩ := NumberedQuotientPathNumericTotalityProof.decoderTotality code
  rw [checkerEvaluation,summaryDecodedEvaluation edge y code parameter entries hentries,
    positiveFinishFoldEvaluation n arity symbols S Gamma table edge parameter hedge]
  unfold positivePathTest
  rw [hentries]
  cases entries <;> rfl

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerEvaluationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerEvaluationProof
