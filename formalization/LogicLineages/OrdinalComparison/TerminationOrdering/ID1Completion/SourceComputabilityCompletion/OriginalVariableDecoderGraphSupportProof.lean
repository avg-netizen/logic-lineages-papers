module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderGraphSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open OriginalVariableDecoder InternalRawListRecursionSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalListCodecSupportProof InternalPositiveUnfoldingSupportProof
open InternalEqualityTestCompositionProof InternalRecursionGraphStepSyntaxProof InternalOriginalOrderProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

abbrev inputs (typ index gamma : OTerm alpha) : Fin 3 → OTerm alpha :=
  Fin.cons typ (Fin.cons index (Fin.cons gamma Fin.elim0))

@[simp] theorem graphRename {beta : Type} (out typ index gamma : OTerm alpha) (j : alpha → beta) :
    (graph out typ index gamma).relabel j =
      graph (out.relabel j) (typ.relabel j) (index.relabel j) (gamma.relabel j) := by
  simp only [graph,programRename,consTermRename,emptyRename]

theorem restValue (typ index gamma residual : OTerm alpha)
    (hd : Nonempty (Derivation body Gamma (dropGraph residual index gamma))) :
    Nonempty (Derivation body Gamma (programGraph rest residual (inputs typ index gamma))) := by
  apply compositionValue InternalRawListRecursion.drop
    (Fin.cons (.projection 1) (Fin.cons (.projection 2) Fin.elim0)) residual
    (inputs typ index gamma) (Fin.cons index (Fin.cons gamma Fin.elim0)) hd
  intro i
  exact Fin.cases (projectionValue 1 (inputs typ index gamma))
    (Fin.cases (projectionValue 2 (inputs typ index gamma)) (fun j => Fin.elim0 j)) i

theorem headValue (typ index gamma residual value : OTerm alpha)
    (hd : Nonempty (Derivation body Gamma (dropGraph residual index gamma)))
    (hh : Nonempty (Derivation body Gamma (unaryGraph InternalListCodec.headCode value residual))) :
    Nonempty (Derivation body Gamma (programGraph head value (inputs typ index gamma))) := by
  apply compositionValue InternalListCodec.headCode (fun _ : Fin 1 => rest) value
    (inputs typ index gamma) (Fin.cons residual Fin.elim0) hh
  intro i
  obtain rfl := Fin.eq_zero i
  exact restValue typ index gamma residual hd

theorem matchesValue (typ index gamma residual value out : OTerm alpha)
    (hd : Nonempty (Derivation body Gamma (dropGraph residual index gamma)))
    (hh : Nonempty (Derivation body Gamma (unaryGraph InternalListCodec.headCode value residual)))
    (he : Nonempty (Derivation body Gamma (equalityGraph out typ value))) :
    Nonempty (Derivation body Gamma (programGraph matchesType out (inputs typ index gamma))) := by
  apply compositionValue InternalEqualityTest.equalityTest
    (Fin.cons (.projection 0) (Fin.cons head Fin.elim0)) out (inputs typ index gamma)
    (Fin.cons typ (Fin.cons value Fin.elim0)) he
  intro i
  exact Fin.cases (projectionValue 0 (inputs typ index gamma))
    (Fin.cases (headValue typ index gamma residual value hd hh) (fun j => Fin.elim0 j)) i

theorem zeroValueAt (xs : Fin 3 → OTerm alpha) :
    Nonempty (Derivation body Gamma (programGraph (InternalAcceptance.constantZero 3) z xs)) :=
  InternalRawListRecursionSupportProof.constantZero xs

/-- Every actual child output is retained in the literal conditional graph. -/
theorem checkValue (out typ index gamma residual value matched : OTerm alpha)
    (hd : Nonempty (Derivation body Gamma (dropGraph residual index gamma)))
    (hh : Nonempty (Derivation body Gamma (unaryGraph InternalListCodec.headCode value residual)))
    (he : Nonempty (Derivation body Gamma (equalityGraph matched typ value)))
    (hc : Nonempty (Derivation body Gamma (programGraph GorbowPRInternalControl.conditional out
      (Fin.cons residual (Fin.cons z (Fin.cons matched Fin.elim0)))))) :
    Nonempty (Derivation body Gamma (graph out typ index gamma)) := by
  exact branchValue rest (InternalAcceptance.constantZero 3) matchesType out residual z matched
    (inputs typ index gamma) (restValue typ index gamma residual hd)
    (zeroValueAt _) (matchesValue typ index gamma residual value matched hd hh he) hc

/-- Inversion uses original composition totality and functionality, never
native evaluation or an asserted semantic correctness premise. -/
theorem checkRecover (out typ index gamma residual value matched : OTerm alpha)
    (hd : Nonempty (Derivation body Gamma (dropGraph residual index gamma)))
    (hh : Nonempty (Derivation body Gamma (unaryGraph InternalListCodec.headCode value residual)))
    (he : Nonempty (Derivation body Gamma (equalityGraph matched typ value)))
    (hw : Nonempty (Derivation body Gamma (graph out typ index gamma))) :
    Nonempty (Derivation body Gamma (programGraph GorbowPRInternalControl.conditional out
      (Fin.cons residual (Fin.cons z (Fin.cons matched Fin.elim0))))) := by
  apply compositionRecover GorbowPRInternalControl.conditional
    (Fin.cons rest (Fin.cons (InternalAcceptance.constantZero 3) (Fin.cons matchesType Fin.elim0)))
    out (inputs typ index gamma) (Fin.cons residual (Fin.cons z (Fin.cons matched Fin.elim0))) hw
  intro i
  exact Fin.cases (restValue typ index gamma residual hd)
    (Fin.cases (zeroValueAt _) (Fin.cases
      (matchesValue typ index gamma residual value matched hd hh he) (fun j => Fin.elim0 j))) i

/-- Same residual context and same requested type give the same entire
checker graph, including rejection and arbitrary output. -/
theorem checkTransfer (out typ index gamma otherIndex otherGamma residual : OTerm alpha)
    (hd : Nonempty (Derivation body Gamma (dropGraph residual index gamma)))
    (ho : Nonempty (Derivation body Gamma (dropGraph residual otherIndex otherGamma)))
    (hw : Nonempty (Derivation body Gamma (graph out typ index gamma))) :
    Nonempty (Derivation body Gamma (graph out typ otherIndex otherGamma)) := by
  apply programCases InternalListCodec.headCode (Fin.cons residual Fin.elim0) _
  intro beta j Delta value hj hh
  rw [graphRename]
  have hd' := renameInto hd j Delta hj
  have ho' := renameInto ho j Delta hj
  have hw' := renameInto hw j Delta hj
  simp only [dropRename,graphRename] at hd' ho' hw'
  simp only [consTermRename,emptyRename] at hh
  apply programCases InternalEqualityTest.equalityTest
    (Fin.cons (typ.relabel j) (Fin.cons value Fin.elim0)) _
  intro beta' k Theta matched hk he
  rw [graphRename]
  have hd'' := renameInto hd' k Theta hk
  have ho'' := renameInto ho' k Theta hk
  have hw'' := renameInto hw' k Theta hk
  have hh' := renameInto hh k Theta hk
  simp only [dropRename,graphRename,programRename,consTermRename,emptyRename] at hd'' ho'' hw'' hh'
  simp only [consTermRename,emptyRename] at he
  exact checkValue _ _ _ _ _ _ matched ho'' hh' he
    (checkRecover _ _ _ _ _ _ matched hd'' hh' he hw'')

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderGraphSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderGraphSupportProof
