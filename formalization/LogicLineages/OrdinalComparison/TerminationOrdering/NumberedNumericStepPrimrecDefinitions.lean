module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformSelectorDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCodecPrimrecProof

@[expose] public section
/-! Context-uniform effectivity of the unchanged numeric step-certificate checker.

Paper06's arithmetic auxiliary relation uses actual auxiliary steps under the
contexts permitted by the source rules (lines551–556 before lem:id1 and
lem:simulation at lines625–658; source SHA256
bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e).
The structural computation below follows the original focus, replacement,
selector and reconstruction checks. A lambda focus changes the context used by
both the replacement decoder and the Mul-selector certificate decoder. Gamma
therefore remains an ordinary joint input throughout the primitive computation.

The numeric wrapper keeps the original source-universe decoding, ordinary
typed target decoding, step-certificate decoding and endpoint type equality.
At the focused hole, the selector retains its original unguarded semantics.
Replacement keeps the exact source siblings, annotations and binder order;
its output code is compared with the requested target code. Calibration must
identify this comparison with the original packed-number comparison.

The exact primitive target is the existing numericStepTest on arbitrary window
lists, contexts, finite Boolean tables and natural inputs. Only n and arity are
fixed. No validity, closure, membership or precedence assumptions are added.
This does not assert arithmetic formula representation, edge/path effectivity,
the complete source simulation lemma, accessibility or ordinal bounds.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrec
open Source NumberedAuxiliaryCoding NumberedUniformPackedDecoding
open NumberedFocusCode NumberedUniformSelector NumberedStepCertificate NumberedNumericStep

/-- Literal focused checking using the actual context and result type at the hole. -/
def stepCodeTest (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (tau : Ty) (source target : Code (Fin n)) (certificate : StepCertificate) : Bool :=
  (focusCode certificate.path Gamma tau source).any (fun focused =>
    (rawPackedDecode n arity focused.1 certificate.replacement).any (fun replacement =>
      if replacement.1 = focused.2.1 then
        selectorCodeTest n arity symbols S focused.1 table
          (focused.2.1,focused.2.2) replacement certificate.root &&
          decide (replaceCode certificate.path Gamma tau source replacement.2 = some target)
      else false))

/-- The original numeric wrapper expressed through the calibrated raw decoders. -/
def numericStepDispatch (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (source target certificate : Nat) : Bool :=
  match rawUniverseDecode n arity symbols S Gamma source,
      rawPackedDecode n arity Gamma target, decodeStepCertificate certificate with
  | some (tau,q), some (sigma,r), some data =>
      if sigma = tau then stepCodeTest n arity symbols S Gamma table tau q r data else false
  | _, _, _ => false

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrec
