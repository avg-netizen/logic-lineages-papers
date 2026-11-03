module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryCodingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryEnumeration
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedAuxiliaryCoding

def typeLists (S : List Ty) : Nat → List (List Ty)
  | 0 => [[]]
  | n+1 => [] :: S.flatMap (fun tau => (typeLists S n).map (List.cons tau))

def depth {Symbol : Type} : Code Symbol → Nat
  | .var _ | .bottom _ | .argumentsNil => 1
  | .lam _ b | .ordinary _ b => 1+depth b
  | .app _ q a | .argumentsCons _ q a => 1+max (depth q) (depth a)
  | .numbered _ _ _ b _ e => 1+max (depth b) (depth e)

def Fields {Symbol : Type} (S : List Ty) (H : List (HeadCode Symbol)) (labels tupleBound : Nat) : Nat → Code Symbol → Prop
  | variableBound,.var i => i<variableBound
  | variableBound,.lam sigma body => sigma∈S ∧ Fields S H labels tupleBound (variableBound+1) body
  | variableBound,.app sigma q a => sigma∈S ∧ Fields S H labels tupleBound variableBound q ∧ Fields S H labels tupleBound variableBound a
  | _,.bottom tau => tau∈S
  | variableBound,.ordinary f base => f∈H ∧ Fields S H labels tupleBound variableBound base
  | variableBound,.numbered k f tau base types extras => k≤labels ∧ f∈H ∧ tau∈S ∧
      Fields S H labels tupleBound variableBound base ∧ types.length≤tupleBound ∧
      (∀ t∈types,t∈S) ∧ Fields S H labels tupleBound variableBound extras
  | _,.argumentsNil => True
  | variableBound,.argumentsCons tau q rest => tau∈S ∧ Fields S H labels tupleBound variableBound q ∧ Fields S H labels tupleBound variableBound rest

def enumerate {Symbol : Type} (S : List Ty) (H : List (HeadCode Symbol)) (labels tupleBound : Nat) : Nat → Nat → List (Code Symbol)
  | _,0 => []
  | variableBound,fuel+1 =>
    let prior := enumerate S H labels tupleBound variableBound fuel
    let opened := enumerate S H labels tupleBound (variableBound+1) fuel
    (List.range variableBound).map Code.var ++
    S.flatMap (fun sigma => opened.map (Code.lam sigma)) ++
    S.flatMap (fun sigma => prior.flatMap (fun q => prior.map (Code.app sigma q))) ++
    S.map Code.bottom ++
    H.flatMap (fun f => prior.map (Code.ordinary f)) ++
    (List.range (labels+1)).flatMap (fun k => H.flatMap (fun f => S.flatMap (fun tau =>
      prior.flatMap (fun b => (typeLists S tupleBound).flatMap (fun types => prior.map (Code.numbered k f tau b types)))))) ++
    [Code.argumentsNil] ++
    S.flatMap (fun tau => prior.flatMap (fun q => prior.map (Code.argumentsCons tau q)))

def sourceHeads {Symbol : Type} [DecidableEq Symbol] (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) : List (HeadCode Symbol) :=
  (headWindow arity symbols S).map headCode

def classCodes {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    {Gamma : List Ty} (q : Packed Symbol arity Gamma) : List (Ty × Code Symbol) :=
  (enumerate S (sourceHeads arity symbols S) (maxLabel q.2) (NumberedPrimaryEquivalence.size q.2)
    Gamma.length (2*NumberedPrimaryEquivalence.size q.2)).map (fun c => (q.1,c))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryEnumeration
