module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorRankProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorLeafRebuildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open OriginalRawSyntaxTransportInternalConstructorRankProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- This records total rebuild behavior even for leaf tags. The traversal
never places leaf return frames, but the frozen rebuild AST remains total. -/
def LeafRebuildResult (mode : Mode) (out raw first second : OTerm alpha) : Formula alpha :=
  match mode with
  | .rank => graph2 InternalArithmeticPrograms.addition out first second
  | .shift | .erase => equal out raw

theorem variableShiftRebuildForward (raw out index first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph variableConstructor raw (Fin.cons index Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild .shift) out raw first second))) :
    Nonempty (Derivation body Delta (equal out raw)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  have ht := variableTag (.projection 0) raw index xs (projectionValue 0 xs) hc
  have h1 := branchNumeralElim 0 1 (leftOf (.projection 0)) _ _ out xs ht ho
  have h2 := branchNumeralElim 0 2 (leftOf (.projection 0)) _ _ out xs ht h1
  have h4 := branchNumeralElim 0 4 (leftOf (.projection 0)) _ _ out xs ht h2
  have h5 := branchNumeralElim 0 5 (leftOf (.projection 0)) _ _ out xs ht h4
  have h7 := branchNumeralElim 0 7 (leftOf (.projection 0)) _ _ out xs ht h5
  simpa only [equalEqn] using valueUnique (.projection 0) out raw xs h7 (projectionValue 0 xs)

theorem variableShiftRebuildBackward (raw out index first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph variableConstructor raw (Fin.cons index Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (equal out raw))) :
    Nonempty (Derivation body Delta (graph3 (rebuild .shift) out raw first second)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  have ht := variableTag (.projection 0) raw index xs (projectionValue 0 xs) hc
  apply branchNumeralIntro 0 1 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 0 2 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 0 4 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 0 5 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 0 7 (leftOf (.projection 0)) _ _ out xs ht
  obtain ⟨he⟩ := ho
  exact outputTransport (.projection 0) raw out xs
    ⟨symm (by simpa only [equalEqn] using he)⟩ (projectionValue 0 xs)

theorem variableRebuildForward (mode : Mode) (raw out index first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph variableConstructor raw (Fin.cons index Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild mode) out raw first second))) :
    Nonempty (Derivation body Delta (LeafRebuildResult mode out raw first second)) := by
  cases mode with
  | shift => exact variableShiftRebuildForward raw out index first second hc ho
  | erase => exact variableShiftRebuildForward raw out index first second hc ho
  | rank =>
    let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
    have ha := variableArity (.projection 0) raw index xs (projectionValue 0 xs) hc
    exact nonunaryRankForward 0 (by decide) raw first second out ha ho

theorem variableRebuildBackward (mode : Mode) (raw out index first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph variableConstructor raw (Fin.cons index Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (LeafRebuildResult mode out raw first second))) :
    Nonempty (Derivation body Delta (graph3 (rebuild mode) out raw first second)) := by
  cases mode with
  | shift => exact variableShiftRebuildBackward raw out index first second hc ho
  | erase => exact variableShiftRebuildBackward raw out index first second hc ho
  | rank =>
    let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
    have ha := variableArity (.projection 0) raw index xs (projectionValue 0 xs) hc
    exact nonunaryRankBackward 0 (by decide) raw first second out ha ho

theorem bottomShiftRebuildForward (raw out tau first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph bottomConstructor raw (Fin.cons tau Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild .shift) out raw first second))) :
    Nonempty (Derivation body Delta (equal out raw)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  have ht := bottomTag (.projection 0) raw tau xs (projectionValue 0 xs) hc
  have h1 := branchNumeralElim 3 1 (leftOf (.projection 0)) _ _ out xs ht ho
  have h2 := branchNumeralElim 3 2 (leftOf (.projection 0)) _ _ out xs ht h1
  have h4 := branchNumeralElim 3 4 (leftOf (.projection 0)) _ _ out xs ht h2
  have h5 := branchNumeralElim 3 5 (leftOf (.projection 0)) _ _ out xs ht h4
  have h7 := branchNumeralElim 3 7 (leftOf (.projection 0)) _ _ out xs ht h5
  simpa only [equalEqn] using valueUnique (.projection 0) out raw xs h7 (projectionValue 0 xs)

theorem bottomShiftRebuildBackward (raw out tau first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph bottomConstructor raw (Fin.cons tau Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (equal out raw))) :
    Nonempty (Derivation body Delta (graph3 (rebuild .shift) out raw first second)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  have ht := bottomTag (.projection 0) raw tau xs (projectionValue 0 xs) hc
  apply branchNumeralIntro 3 1 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 3 2 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 3 4 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 3 5 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 3 7 (leftOf (.projection 0)) _ _ out xs ht
  obtain ⟨he⟩ := ho
  exact outputTransport (.projection 0) raw out xs
    ⟨symm (by simpa only [equalEqn] using he)⟩ (projectionValue 0 xs)

theorem bottomRebuildForward (mode : Mode) (raw out tau first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph bottomConstructor raw (Fin.cons tau Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild mode) out raw first second))) :
    Nonempty (Derivation body Delta (LeafRebuildResult mode out raw first second)) := by
  cases mode with
  | shift => exact bottomShiftRebuildForward raw out tau first second hc ho
  | erase => exact bottomShiftRebuildForward raw out tau first second hc ho
  | rank =>
    let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
    have ha := bottomArity (.projection 0) raw tau xs (projectionValue 0 xs) hc
    exact nonunaryRankForward 0 (by decide) raw first second out ha ho

theorem bottomRebuildBackward (mode : Mode) (raw out tau first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph bottomConstructor raw (Fin.cons tau Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (LeafRebuildResult mode out raw first second))) :
    Nonempty (Derivation body Delta (graph3 (rebuild mode) out raw first second)) := by
  cases mode with
  | shift => exact bottomShiftRebuildBackward raw out tau first second hc ho
  | erase => exact bottomShiftRebuildBackward raw out tau first second hc ho
  | rank =>
    let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
    have ha := bottomArity (.projection 0) raw tau xs (projectionValue 0 xs) hc
    exact nonunaryRankBackward 0 (by decide) raw first second out ha ho

theorem nilShiftRebuildForward (raw out  first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw (Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild .shift) out raw first second))) :
    Nonempty (Derivation body Delta (equal out raw)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  have ht := nilTag (.projection 0) raw  xs (projectionValue 0 xs) hc
  have h1 := branchNumeralElim 6 1 (leftOf (.projection 0)) _ _ out xs ht ho
  have h2 := branchNumeralElim 6 2 (leftOf (.projection 0)) _ _ out xs ht h1
  have h4 := branchNumeralElim 6 4 (leftOf (.projection 0)) _ _ out xs ht h2
  have h5 := branchNumeralElim 6 5 (leftOf (.projection 0)) _ _ out xs ht h4
  have h7 := branchNumeralElim 6 7 (leftOf (.projection 0)) _ _ out xs ht h5
  simpa only [equalEqn] using valueUnique (.projection 0) out raw xs h7 (projectionValue 0 xs)

theorem nilShiftRebuildBackward (raw out  first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw (Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (equal out raw))) :
    Nonempty (Derivation body Delta (graph3 (rebuild .shift) out raw first second)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  have ht := nilTag (.projection 0) raw  xs (projectionValue 0 xs) hc
  apply branchNumeralIntro 6 1 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 6 2 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 6 4 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 6 5 (leftOf (.projection 0)) _ _ out xs ht
  apply branchNumeralIntro 6 7 (leftOf (.projection 0)) _ _ out xs ht
  obtain ⟨he⟩ := ho
  exact outputTransport (.projection 0) raw out xs
    ⟨symm (by simpa only [equalEqn] using he)⟩ (projectionValue 0 xs)

theorem nilRebuildForward (mode : Mode) (raw out  first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw (Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild mode) out raw first second))) :
    Nonempty (Derivation body Delta (LeafRebuildResult mode out raw first second)) := by
  cases mode with
  | shift => exact nilShiftRebuildForward raw out  first second hc ho
  | erase => exact nilShiftRebuildForward raw out  first second hc ho
  | rank =>
    let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
    have ha := nilArity (.projection 0) raw  xs (projectionValue 0 xs) hc
    exact nonunaryRankForward 0 (by decide) raw first second out ha ho

theorem nilRebuildBackward (mode : Mode) (raw out  first second : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw (Fin.elim0))))
    (ho : Nonempty (Derivation body Delta (LeafRebuildResult mode out raw first second))) :
    Nonempty (Derivation body Delta (graph3 (rebuild mode) out raw first second)) := by
  cases mode with
  | shift => exact nilShiftRebuildBackward raw out  first second hc ho
  | erase => exact nilShiftRebuildBackward raw out  first second hc ho
  | rank =>
    let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
    have ha := nilArity (.projection 0) raw  xs (projectionValue 0 xs) hc
    exact nonunaryRankBackward 0 (by decide) raw first second out ha ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorLeafRebuildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorLeafRebuildProof
