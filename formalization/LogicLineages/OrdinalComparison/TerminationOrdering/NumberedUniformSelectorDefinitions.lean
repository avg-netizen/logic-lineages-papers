module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMulDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecodingDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyOperationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRootDefinitions

@[expose] public section
/-! Context-uniform computation for the original decoded selector test.

Paper06's arithmetic auxiliary relation requires the local root decision at a
focused occurrence, whose context changes below binders. This component retains
the original selector tags, malformed-payload behavior, operation outputs and
Mul certificate decoding. The source correspondence is to the root rules used
before lem:id1 (lines551–556) and by lem:simulation (lines625–658); source SHA256
bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e.

The original selectorTest is unguarded: source-universe decoding belongs to the
outer numeric root or step checker. Accordingly this computation adds no source
membership, type-closure or precedence hypothesis. Direct, Select and Copy
retain their actual source result type in the raw output pair. Mul uses its
original context-dependent certificate decoder through the separately specified
uniform raw computation. The calibration quantifies over every actual packed
endpoint and every certificate natural. The primitive-recursion target varies
Gamma, both windows, the finite precedence table, both raw endpoints and the
certificate jointly, with only n and arity fixed.

No whole arithmetic formula, complete source simulation, accessibility or
ordinal-bound claim is made by these two selector targets.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformSelector
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedNumericDecoding
open NumberedUniformPackedDecoding NumberedDirectOperations NumberedAuxiliarySubstitution
open NumberedSelfApplication NumberedCopyOperation

/-- Compare the literal output code with the requested type/code pair. -/
def outputCodeTest {n : Nat} (tau : Ty) (output : Option (Code (Fin n)))
    (target : RawPacked n) : Bool :=
  decide (output.map (fun code => (tau,code)) = some target)

/-- The unchanged decoded-selector branches on context-independent structural data. -/
def selectorCodeTest (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (source target : RawPacked n) (certificate : Nat) : Bool :=
  match Nat.unpair certificate with
  | (0,label) => outputCodeTest source.1 (putCode label source.1 source.2) target
  | (1,0) => outputCodeTest source.1 (abstractionCode source.2) target
  | (2,0) => outputCodeTest source.1 (betaCode Gamma.length source.2) target
  | (3,0) => outputCodeTest source.1 (bottomCode source.1 source.2) target
  | (4,payload) => (decodeTypes (Nat.unpair payload).1).any (fun types =>
      outputCodeTest source.1
        (selectCode types (Nat.unpair payload).2 source.1 source.2) target)
  | (5,payload) => (decodeHeadNumber n payload).any (fun head =>
      outputCodeTest source.1 (copyCode arity symbols S table head source.2) target)
  | (6,payload) => NumberedUniformMul.mulTest n arity symbols S Gamma source.2 target.2 payload
  | _ => false

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformSelector
