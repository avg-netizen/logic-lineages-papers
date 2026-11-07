module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftEdgeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.PositiveTypedCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathCertificatesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPath
open Source NumberedQuotientPathCertificates

/-- Recanonicalize an original vertex using the ORIGINAL decoded application,
with the caller's unchanged context code and the fixed original argument. -/
def vertex (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context domain codomain argument value : Nat) : Nat :=
  (OrdinaryArithmeticApplication.decodedApplication n arity Gamma
    context domain codomain value argument).getD 0

/-- Preserve one edge for each original edge, recanonicalizing only its next
vertex and applying the explicit original edge-certificate transformer. -/
def liftEntries (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context domain codomain argument : Nat) (entries : List EdgeEntry) : List EdgeEntry :=
  entries.map (fun entry =>
    (vertex n arity Gamma context domain codomain argument entry.1,
      ApplicationCertificateLiftEdge.liftEdge domain codomain argument entry.2))

/-- The ORIGINAL path encoder/decoder. The empty-list default is off-domain;
positive acceptance is proved only from the original checker premises. -/
def liftPath (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context domain codomain argument certificate : Nat) : Nat :=
  pathCertificateNumber (liftEntries n arity Gamma context domain codomain argument
    ((decodePathCertificate certificate).getD []))

/-- K(context,domain,codomain,argument,certificate). The original argument
object supplies Gamma and its canonical payload. It does not depend on the
source or target object and is total on all five natural inputs. -/
def pathValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 5) : Nat :=
  ((Encodable.decode (α := ContextUniform.Object) (v.get 3)).map (fun a =>
    liftPath n arity a.1 (v.get 0) (v.get 1) (v.get 2) a.2 (v.get 4))).getD 0

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPath
