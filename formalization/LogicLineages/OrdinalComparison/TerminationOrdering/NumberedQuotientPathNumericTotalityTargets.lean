module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathNumericTotalityTargets
open Source NumberedQuotientPathCertificates ID1Completion.ApplicationCertificateLiftPath

/-- Every natural code decodes to exactly one list of original edge entries.
This is a coding theorem, not acceptance by the typed path checker. -/
def ActualPathUniqueDecoding : Prop :=
  ∀ certificate : Nat, ∃! entries : List EdgeEntry,
    decodePathCertificate certificate = some entries

/-- Both inverse equations for the unchanged source encoder and decoder.
The second equation applies to every natural input. -/
def ActualPathCodingInverse : Prop :=
  (∀ entries : List EdgeEntry,
    decodePathCertificate (pathCertificateNumber entries) = some entries) ∧
  (∀ certificate : Nat,
    pathCertificateNumber ((decodePathCertificate certificate).getD []) = certificate)

def ActualPathEncodingBijection : Prop :=
  Function.Bijective pathCertificateNumber

def ActualPathDecoderEquation : Prop :=
  ∀ (certificate : Nat) (entries : List EdgeEntry),
    decodePathCertificate certificate = some entries ↔
      pathCertificateNumber entries = certificate

/-- Literal nil and successor-of-pair equations, with an arbitrary raw tail
code. No successful-decoding or source-validity hypothesis is supplied. -/
def ActualPathDecoderStructure : Prop :=
  decodePathCertificate 0 = some [] ∧
  ∀ value edge tail : Nat,
    decodePathCertificate (1 + Nat.pair (Nat.pair value edge) tail) =
      (decodePathCertificate tail).map ((value,edge) :: ·)

/-- The existing application transformer commutes with the actual path
decoder on every code, including certificates rejected by the source checker. -/
def ActualLiftPathDecoder : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context domain codomain argument certificate : Nat),
    decodePathCertificate (liftPath n arity Gamma context domain codomain argument certificate) =
      (decodePathCertificate certificate).map
        (liftEntries n arity Gamma context domain codomain argument)

/-- Decoded length is preserved on all natural codes, without any typed
application or positive-path premise. -/
def ActualLiftPathLength : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context domain codomain argument certificate : Nat),
    ((decodePathCertificate
      (liftPath n arity Gamma context domain codomain argument certificate)).getD []).length =
      ((decodePathCertificate certificate).getD []).length

/-- Empty decoded paths and their literal zero code are preserved and
reflected by the original application transformer. -/
def ActualLiftPathEmpty : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context domain codomain argument certificate : Nat),
    (decodePathCertificate (liftPath n arity Gamma context domain codomain argument certificate) =
        some [] ↔ decodePathCertificate certificate = some []) ∧
    (liftPath n arity Gamma context domain codomain argument certificate = 0 ↔ certificate = 0)

/-- Exact constructor equations for the original transformer. The next
vertex uses its original canonical application builder, the edge certificate
uses its original liftEdge, and the tail is the unchanged raw path code. -/
def ActualLiftPathStructure : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context domain codomain argument : Nat),
    liftPath n arity Gamma context domain codomain argument 0 = 0 ∧
    ∀ value edge tail : Nat,
      liftPath n arity Gamma context domain codomain argument
        (1 + Nat.pair (Nat.pair value edge) tail) =
      1 + Nat.pair
        (Nat.pair (vertex n arity Gamma context domain codomain argument value)
          (ID1Completion.ApplicationCertificateLiftEdge.liftEdge domain codomain argument edge))
        (liftPath n arity Gamma context domain codomain argument tail)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathNumericTotalityTargets
