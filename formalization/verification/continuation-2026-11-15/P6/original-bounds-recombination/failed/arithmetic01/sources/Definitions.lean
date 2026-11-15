module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport
/-- Exact Nat maximum: select the second input precisely when first<second. -/
def maximum : Program 2 := InternalAcceptance.branch InternalLessThan.ltTest (.projection 0) (.projection 1)
/-- Original mergeBounds on the original Nat.pair encoding, for arbitrary inputs. -/
def merge : Program 2 := pairOf
  (addOf (leftOf (.projection 0)) (leftOf (.projection 1)))
  (.composition maximum ![rightOf (.projection 0),rightOf (.projection 1)])
/-- Original ordered foldr, with encoded (0,0) base. -/
def collect : Program 1 := InternalRawListRecursion.listRec (constant 0 0) merge
/-- Root contribution: list constructors contribute zero, numbered contributes
(1,k), all other admitted constructors (1,0). Actual decoder failure returns0. -/
def root (n : Nat) : Program 1 :=
  InternalAcceptance.branch (OriginalCodeValidityGuard.check n) (constant 1 0)
    (Continuation20261114.OriginalHeadEncodingBridge.choose 6 (constant 1 0)
      (Continuation20261114.OriginalHeadEncodingBridge.choose 7 (constant 1 0)
        (Continuation20261114.OriginalHeadEncodingBridge.choose 5
          (pairOf (constant 1 1) (leftOf InternalUnpair.right))
          (pairOf (constant 1 1) (constant 1 0)))))
/-- Exact recombination returns Some(encoded bounds), hence successor payload.
Invalid raw code explicitly extends the source function by None=0. -/
def recombine (n : Nat) : Program 2 :=
  InternalAcceptance.branch
    (.composition (OriginalCodeValidityGuard.check n) (fun _ : Fin 1 => .projection 0))
    (constant 2 0)
    (.composition .succ (fun _ : Fin 1 =>
      .composition merge ![.composition (root n) (fun _ : Fin 1 => .projection 0),
        .composition collect (fun _ : Fin 1 => .projection 1)]))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination
