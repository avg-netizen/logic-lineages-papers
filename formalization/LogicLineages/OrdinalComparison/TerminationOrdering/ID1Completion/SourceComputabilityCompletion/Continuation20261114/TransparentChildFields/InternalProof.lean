module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof OriginalRawSyntaxTransportInternalConstructorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem guarded (V q : Program 3) (out node code param : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)))
    (hq : Nonempty (Derivation body Delta (graph3 q out node code param))) :
    Nonempty (Derivation body Delta
      (graph3 (InternalAcceptance.branch V (constant 3 0) q) out node code param)) :=
  successorBranchIntro V (constant 3 0) q out z ![node,code,param] hv hq

theorem internalLambda : Targets.InternalLambda := by
  intro body alpha Delta V target node code param raw domain child hV hq hc
  let xs : Fin 3 → OTerm alpha := ![node,code,param]
  have ha := lambdaArity (rawCode target) raw domain child xs hq hc
  have hf := lambdaFirst (rawCode target) raw domain child xs hq hc
  have hfirst : Nonempty (Derivation body Delta (graph3 (firstRaw target) child node code param)) :=
    successorBranchIntro (arityOf (rawCode target)) (constant 3 0) (firstOf (rawCode target)) child z xs ha hf
  have hsecond : Nonempty (Derivation body Delta (graph3 (secondRaw target) (numeral 0) node code param)) := by
    apply branchNumeralIntro 1 2 (arityOf (rawCode target)) (constant 3 0) (secondOf (rawCode target)) (numeral 0) xs ha
    exact constantValue 0 xs
  exact ⟨guarded V (firstRaw target) child node code param hV hfirst,
    guarded V (secondRaw target) (numeral 0) node code param hV hsecond⟩

theorem binaryChildren (V : Program 3) (target : Bool)
    (node code param left right : OTerm alpha)
    (hV : Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)))
    (ha : Nonempty (Derivation body Delta (graph3 (arityOf (rawCode target)) (numeral 2) node code param)))
    (hl : Nonempty (Derivation body Delta (graph3 (firstOf (rawCode target)) left node code param)))
    (hr : Nonempty (Derivation body Delta (graph3 (secondOf (rawCode target)) right node code param))) :
    Nonempty (Derivation body Delta (graph3 (first V target) left node code param)) ∧
    Nonempty (Derivation body Delta (graph3 (second V target) right node code param)) := by
  let xs : Fin 3 → OTerm alpha := ![node,code,param]
  have hfirst : Nonempty (Derivation body Delta (graph3 (firstRaw target) left node code param)) :=
    successorBranchIntro (arityOf (rawCode target)) (constant 3 0) (firstOf (rawCode target)) left (numeral 1) xs ha hl
  have hsecond : Nonempty (Derivation body Delta (graph3 (secondRaw target) right node code param)) := by
    apply branchNumeralIntro 2 2 (arityOf (rawCode target)) (constant 3 0) (secondOf (rawCode target)) right xs ha
    exact hr
  exact ⟨guarded V (firstRaw target) left node code param hV hfirst,
    guarded V (secondRaw target) right node code param hV hsecond⟩

theorem internalApplication : Targets.InternalApplication := by
  intro body alpha Delta V target cons node code param raw domain left right hV hq hc
  let xs : Fin 3 → OTerm alpha := ![node,code,param]
  cases cons with
  | false =>
    exact binaryChildren V target node code param left right hV
      (applicationArity (rawCode target) raw domain left right xs hq hc)
      (applicationFirst (rawCode target) raw domain left right xs hq hc)
      (applicationSecond (rawCode target) raw domain left right xs hq hc)
  | true =>
    exact binaryChildren V target node code param left right hV
      (consArity (rawCode target) raw domain left right xs hq hc)
      (consFirst (rawCode target) raw domain left right xs hq hc)
      (consSecond (rawCode target) raw domain left right xs hq hc)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields.InternalProof
