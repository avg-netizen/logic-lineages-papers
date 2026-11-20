import LogicLineages.PersistentMarking.NumberedWindowAdmissionAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCode
import LogicLineages.PersistentMarking.NumberedWindowTypingBits

namespace LogicLineages.PersistentMarking.NumberedWindowAdmissionTargets
open NumberedWindowAdmissionAlgorithm NumberedWindowSyntax NumberedWindowDomain
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode
open NumberedWindowHeadEnumerationTargets (admittedHeads headBit)
open TypeSupport (subtypes)

def typesIn (K : List Ty) (ts : List Ty) : Bool :=
  ts.all (fun τ => decide (τ ∈ K))

/-- These are finite constants for the fixed symbolic signature and window. -/
def window (S : Spine.Signature) (K : List Ty) : Window :=
  ((K.filter (fun σ => typesIn K (subtypes σ))).map encodeTy,
    (admittedHeads S K).map encodeHead)

def termGuard (S : Spine.Signature) (K : List Ty) (q : NTerm) : Bool :=
  typesIn K (support q) && (heads q).all (headBit S K)

def argsGuard (S : Spine.Signature) (K : List Ty) (qs : NArgs) : Bool :=
  typesIn K (argsSupport qs) && (argsHeads qs).all (headBit S K)

def WindowConstants : Prop :=
  (∀ S K τ, (window S K).1.contains (encodeTy τ) = typesIn K (subtypes τ)) ∧
  (∀ S K f, (window S K).2.contains (encodeHead f) = headBit S K f)

def LiteralAdmission : Prop :=
  (∀ S K q, (bits (window S K) (encodeTerm q)).1 = termGuard S K q) ∧
  (∀ S K qs, (bits (window S K) (encodeArgs qs)).2 = argsGuard S K qs)

def DecodedAdmission : Prop := ∀ S K n,
  bits (window S K) n =
    ((decodeTerm n).any (termGuard S K), (decodeArgs n).any (argsGuard S K))

end LogicLineages.PersistentMarking.NumberedWindowAdmissionTargets
