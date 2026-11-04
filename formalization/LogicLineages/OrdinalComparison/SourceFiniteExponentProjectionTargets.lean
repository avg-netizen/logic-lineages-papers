module
public import LogicLineages.OrdinalComparison.SourceFiniteExponentProjectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceFiniteExponentProjection.Targets

def ExactCoefficients : Prop :=
  (∀ (g : SignedPair.CantorGroup) (n : Nat),finitePart g n=g (n:Ordinal)) ∧
  (∀ (e : Ordinal) (c : Int),Ordinal.omega0≤e → finitePart (Finsupp.single e c)=0)

def SignedOperations : Prop :=
  finitePart 0=0 ∧
  (∀ g h : SignedPair.CantorGroup,finitePart (g+h)=finitePart g+finitePart h) ∧
  (∀ g : SignedPair.CantorGroup,finitePart (-g)= -finitePart g) ∧
  (∀ (k : Int) (g : SignedPair.CantorGroup),finitePart (k • g)=k • finitePart g)

def ExactShift : Prop := ∀ g : SignedPair.CantorGroup,
  finitePart (SignedPair.omegaShift g)=polynomialShift (finitePart g)

def ExpressionTransport : Prop := ∀ (n : Nat) (x : Fin n → Ordinal) (d : SignedPair.Expression n),
  finitePart (SignedPair.meaning x d)=
    polynomialMeaning (fun i => finitePart (SignedPair.signedCNF (x i))) d
end LogicLineages.OrdinalComparison.Source.SourceFiniteExponentProjection.Targets
