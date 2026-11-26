module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitutionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesDefinitions

@[expose] public section
/-! Original auxiliary beta results for the arithmetic supplier needed by
paper06's lambda paragraph (paper.tex lines 589-595), using the beta rule in
lines 541-549. Source SHA256:
bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e.

This packet concerns native capture-avoiding substitution in the original
auxiliary syntax. It is neither first-order formula substitution nor the
arithmetic beta sequence function. It supplies a candidate external numeric
function and exact contracts, not an internal inference rule. Graph exposure,
transport under source steps, a calibrated final Package and lambda
computability are separate obligations.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResult
open Source NumberedRewriteSyntax NumberedRewriteReduction
open NumberedLeastCodeRepresentative NumberedUniformPackedDecoding NumberedAuxiliarySubstitution
open InternalOriginalUniformParameterLeaves
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The ORIGINAL empty focus path and ORIGINAL beta selector. The supplied
replacement is retained literally, including when it is not a valid code. -/
def rootCertificate (replacement : Nat) : Nat :=
  Nat.pair 0 (Nat.pair replacement (Nat.pair 2 0))

/-- Check the original packed typing decoder, perform the original numeric
capture-avoiding beta operation with precisely Gamma.length free variables,
and encode the output using the ORIGINAL raw packed numbering.

Zero means decoding or beta-shape failure; a successful raw result is its
successor. No source-universe filter is imposed. In particular this function
does not use Encodable.encode on Code, and its result is not an Object code. -/
def rawResult (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (source : Nat) : Nat :=
  ((rawPackedDecode n arity Gamma source).bind (fun raw =>
    (betaCode Gamma.length raw.2).map (fun code =>
      Nat.succ (Nat.pair (typeNumber raw.1) (codeNumber code))))).getD 0

/-- Inputs are the unchanged RAW packed source and the existing parameterCode
pair of original contextCode and Encodable Gamma. The original context and
Object decoders are retained on all inputs, including malformed parameters.
The decoded windows/table do not restrict beta's typed result. -/
def resultValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) : Nat :=
  decodedValue n (fun _ obj => rawResult n arity obj.1 obj.2) (v.get 0) (v.get 1)

/-- All-input calibration of a binary AST, before any windows or Gamma are
chosen. This is external evaluation equality, not an internal graph premise. -/
def Calibrated (n : Nat) (arity : Fin n → Nat) (B : Program 2) : Prop :=
  ∀ v : List.Vector Nat 2, evaluate B v = resultValue n arity v

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResult
