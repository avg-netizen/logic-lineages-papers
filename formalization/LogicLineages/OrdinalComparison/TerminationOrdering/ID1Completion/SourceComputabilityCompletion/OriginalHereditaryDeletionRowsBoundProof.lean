module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsBoundTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsIndexedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsBoundProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalAcceptanceSupportProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open OriginalHereditaryDeletionRows
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem nativeRows : OriginalHereditaryDeletionRowsBoundTargets.NativeRows := by
  intro Q input parameter
  change evaluate (scan Q) (List.Vector.ofFn ![
    evaluate OriginalContextInsertion.length (List.Vector.ofFn ![
      evaluate (rightOf (.projection 1)) (List.Vector.ofFn ![input,parameter])]),input,parameter]) = _
  have hright : evaluate (rightOf (.projection 1)) (List.Vector.ofFn ![input,parameter]) =
      (Nat.unpair parameter).2 := by
    rw [InternalApplicationCertificateConstructorsEvaluationProof.rightOfEvaluation]
    rfl
  rw [hright]
  exact OriginalHereditaryDeletionRowsNativeProof.nativeScan Q _ input parameter

theorem scanFromRows (Q : Program 2) (input parameter gamma count row : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.right gamma parameter)))
    (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count gamma)))
    (hr : Nonempty (Derivation body Delta (graph2 (rows Q) row input parameter))) :
    Nonempty (Derivation body Delta (graph3 (scan Q) row count input parameter)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  let c : Program 2 := .composition OriginalContextInsertion.length
    (fun _ : Fin 1 => rightOf (.projection 1))
  have hright : Nonempty (Derivation body Delta (programGraph (rightOf (.projection 1)) gamma xs)) := by
    apply compositionValue InternalUnpair.right (fun _ : Fin 1 => .projection 1)
      gamma xs (Fin.cons parameter Fin.elim0) hg
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 xs
  have hcount : Nonempty (Derivation body Delta (programGraph c count xs)) := by
    apply compositionValue OriginalContextInsertion.length (fun _ : Fin 1 => rightOf (.projection 1))
      count xs (Fin.cons gamma Fin.elim0) hl
    intro i
    obtain rfl := Fin.eq_zero i
    exact hright
  apply compositionRecover (scan Q) ![c,.projection 0,.projection 1]
    row xs (Fin.cons count (Fin.cons input (Fin.cons parameter Fin.elim0))) hr
  intro i
  exact Fin.cases hcount (Fin.cases (projectionValue 0 xs)
    (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k))) i

theorem indexedRows : OriginalHereditaryDeletionRowsBoundTargets.IndexedRows := by
  intro Q body alpha Delta input parameter gamma count row cutoff out
  let A := graph1 InternalUnpair.right gamma parameter ⊓
    (graph1 OriginalContextInsertion.length count gamma ⊓
      (OriginalContextInsertion.Below cutoff count ⊓
        (graph2 (rows Q) row input parameter ⊓ graph2 InternalRawListRecursion.lookup out cutoff row)))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hs := scanFromRows Q input parameter gamma count row (andLeft h)
    (andLeft (andRight h)) (andLeft (andRight (andRight (andRight h))))
  obtain ⟨hi⟩ := OriginalHereditaryDeletionRowsIndexedProof.actualIndexed Q body alpha (A :: Delta)
    count input parameter row cutoff out
  obtain ⟨hf⟩ := andIntro (andLeft (andRight (andRight h)))
    (andIntro hs (andRight (andRight (andRight (andRight h)))))
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hi hf)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsBoundProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsBoundProof
