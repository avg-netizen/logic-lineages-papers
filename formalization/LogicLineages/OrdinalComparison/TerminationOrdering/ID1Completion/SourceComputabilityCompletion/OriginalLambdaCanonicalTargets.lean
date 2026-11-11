module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedFinitePrimaryClass NumberedLeastCodeRepresentative OriginalLambdaCanonical
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

local instance {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} :
    DecidableEq (Packed (Fin n) arity Gamma) :=
  NumberedAuxiliaryCodingProof.packedDecidableEq

/-- Exact image description of the ORIGINAL finite primary class. Every
member has the same lambda domain and codomain, and its body belongs to the
ORIGINAL primaryClass at sigma::Gamma; conversely every such body occurs.
Closure and confinement are the premises of the existing exact finite-class
supplier. No separate sigma/tau membership or context-window premise is added. -/
def ActualOriginalLambdaPrimaryClassImage : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun rho => rho ∈ S) →
  ∀ (Gamma : List Ty) (sigma tau : Ty)
    (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau),
  InUniverse symbols S (AuxTerm.lam body) →
  ∀ q : Packed (Fin n) arity Gamma,
    q ∈ primaryClass symbols S (lambdaPacked body) ↔
      ∃ body' : AuxTerm (Fin n) arity (sigma :: Gamma) tau,
        q = lambdaPacked body' ∧
          (⟨tau,body'⟩ : Packed (Fin n) arity (sigma :: Gamma)) ∈
            primaryClass symbols S ⟨tau,body⟩

/-- Exact numeric factorization of the ORIGINAL least-code representative.
The right side is the literal packed lambda number, built from the ORIGINAL
least-code body representative. In particular the outer arrow is typeNumber,
the lambda tag is 1, and only the packed body's outer type field is removed.
This is native finite-class mathematics, not internal full-fold coherence. -/
def ActualOriginalLambdaRepresentativeFactorization : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun rho => rho ∈ S) →
  ∀ (Gamma : List Ty) (sigma tau : Ty)
    (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau),
  InUniverse symbols S (AuxTerm.lam body) →
  representativeCode symbols S (lambdaPacked body) =
    Nat.pair (typeNumber (.arrow sigma tau))
      (Nat.pair 1 (Nat.pair (typeNumber sigma)
        (Nat.unpair (representativeCode symbols S ⟨tau,body⟩)).2))

/-- Native fixedness of the ORIGINAL lambda is equivalent to native fixedness
of its ORIGINAL typed body. No transition fixedness, internal canonical
Program, semantic-to-internal reflection or computability premise appears. -/
def ActualOriginalLambdaCanonicalBodyIff : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun rho => rho ∈ S) →
  ∀ (Gamma : List Ty) (sigma tau : Ty)
    (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau),
  InUniverse symbols S (AuxTerm.lam body) →
  (representativeCode symbols S (lambdaPacked body) = packedNumber (lambdaPacked body) ↔
    representativeCode symbols S ⟨tau,body⟩ = packedNumber ⟨tau,body⟩)

/-- Recover one actual body minimizer at the SAME domain, codomain, symbol
window and extended context. Its original lambda is the actual lambda
minimizer. The already fixed constructor and bodyCode ASTs evaluate to these
SAME representative codes. This is a typed native reconstruction only; the
internal graph laws and internal full canonical fold require separate proofs. -/
def ActualOriginalLambdaCanonicalBodySelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun rho => rho ∈ S) →
  ∀ (Gamma : List Ty) (sigma tau : Ty)
    (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau),
  InUniverse symbols S (AuxTerm.lam body) →
  ∃ body' : AuxTerm (Fin n) arity (sigma :: Gamma) tau,
    InUniverse symbols S body' ∧
    (⟨tau,body'⟩ : Packed (Fin n) arity (sigma :: Gamma)) ∈
      primaryClass symbols S ⟨tau,body⟩ ∧
    representativeCode symbols S ⟨tau,body⟩ = packedNumber ⟨tau,body'⟩ ∧
    representativeCode symbols S ⟨tau,body'⟩ = packedNumber ⟨tau,body'⟩ ∧
    representativeCode symbols S (lambdaPacked body) = packedNumber (lambdaPacked body') ∧
    evaluate OriginalLambdaConstructor.bodyCode
      (List.Vector.ofFn ![typeNumber tau,representativeCode symbols S (lambdaPacked body)]) =
        representativeCode symbols S ⟨tau,body⟩ ∧
    evaluate OriginalLambdaConstructor.constructor
      (List.Vector.ofFn ![typeNumber sigma,typeNumber tau,
        representativeCode symbols S ⟨tau,body⟩]) =
          representativeCode symbols S (lambdaPacked body)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonicalTargets
