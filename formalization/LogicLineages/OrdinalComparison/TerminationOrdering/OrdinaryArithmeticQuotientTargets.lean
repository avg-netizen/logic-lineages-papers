module

public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientTargets

open Source OrdinaryArithmetic OrdinaryArithmeticQuotient NumberedQuotientPaths
open NumberedRewriteReduction
open NumberedCopyCertificate
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def EncodedCheckersPrimitive : Prop := ∀ n (arity : Fin n → Nat) (Gamma : List Ty),
  Primrec (edgeValue n arity Gamma) ∧ Primrec (positiveValue n arity Gamma)

def ActualCheckerCalibration : Prop := ∀ n (arity : Fin n → Nat) (Gamma : List Ty)
  (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool) (x y c : Nat),
  edgeValue n arity Gamma (List.Vector.ofFn ![contextCode symbols S table, x, y, c]) =
    (NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table x y c).toNat ∧
  positiveValue n arity Gamma (List.Vector.ofFn ![contextCode symbols S table, x, y, c]) =
    (NumberedQuotientPathCertificates.positivePathTest n arity symbols S Gamma table x y c).toNat

def CertificateGraphTruth : Prop := ∀ (p : Program 4) (v : Fin 3 → Nat),
  (certificateGraph p).Realize v ↔
    ∃ c : Nat, evaluate p (List.Vector.ofFn ![v 0, v 1, v 2, c]) = 1

/-- One pair of real programs works on ALL context codes. Malformed context
codes are rejected. R is the original POSITIVE closure, never its reflexive
closure. Gamma is fixed at precisely the paid checker-effectivity scope. -/
def EncodedHAndPositiveR : Prop := ∀ n (arity : Fin n → Nat) (Gamma : List Ty),
  ∃ pH pR : Program 4,
    (∀ v, evaluate pH v = edgeValue n arity Gamma v) ∧
    (∀ v, evaluate pR v = positiveValue n arity Gamma v) ∧
    (∀ ctxCode x y : Nat,
      (certificateGraph pH).Realize ![ctxCode, x, y] ↔
        ∃ ctx : Context n, Encodable.decode (α := Context n) ctxCode = some ctx ∧
          QuotientEdge n arity ctx.1.1 ctx.1.2 (tableAbove ctx.2) Gamma x y) ∧
    (∀ ctxCode x y : Nat,
      (certificateGraph pR).Realize ![ctxCode, x, y] ↔
        ∃ ctx : Context n, Encodable.decode (α := Context n) ctxCode = some ctx ∧
          PositivePath (QuotientEdge n arity ctx.1.1 ctx.1.2 (tableAbove ctx.2) Gamma) x y)

/-- The SAME pair of arithmetic formulas covers every shared source window
and table; S may therefore be instantiated once as Ty(s) at BOTH endpoints.
This is standard-N representation, not derivability or a norm theorem in ID1. -/
def UniformSharedWindowFormulas : Prop := ∀ n (arity : Fin n → Nat) (Gamma : List Ty),
  ∃ phiH phiR : Formula (Fin 3),
    ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool) (x y : Nat),
      (phiH.Realize ![contextCode symbols S table, x, y] ↔
        QuotientEdge n arity symbols S (tableAbove table) Gamma x y) ∧
      (phiR.Realize ![contextCode symbols S table, x, y] ↔
        PositivePath (QuotientEdge n arity symbols S (tableAbove table) Gamma) x y)

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientTargets
