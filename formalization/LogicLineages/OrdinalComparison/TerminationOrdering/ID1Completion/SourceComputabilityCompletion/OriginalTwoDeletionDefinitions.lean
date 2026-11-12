module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportTypedSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletion
open Source NumberedRewriteSyntax NumberedAuxiliaryCoding
open OriginalRawSyntaxTransport
/-- Only propositional reassociation of the SAME typed context. -/
def castContext {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty} {tau : Ty}
    (h : Gamma = Delta) (q : AuxTerm Symbol arity Gamma tau) : AuxTerm Symbol arity Delta tau := h ▸ q

/-- Delete the earlier cell alpha, then beta at its shifted index. -/
def lowerFirst {Symbol : Type} {arity : Symbol → Nat} (A B Gamma : List Ty) (alpha beta tau : Ty)
    (q : AuxTerm Symbol arity (A ++ alpha :: (B ++ beta :: Gamma)) tau) :
    AuxTerm Symbol arity ((A ++ B) ++ Gamma) tau :=
  substitute
    (castContext (List.append_assoc A B (beta :: Gamma)).symm
      (substitute q (prefixErasure A (B ++ beta :: Gamma) alpha)))
    (prefixErasure (A ++ B) Gamma beta)

/-- Delete beta at its original later index, then the earlier alpha cell. -/
def upperFirst {Symbol : Type} {arity : Symbol → Nat} (A B Gamma : List Ty) (alpha beta tau : Ty)
    (q : AuxTerm Symbol arity (A ++ alpha :: (B ++ beta :: Gamma)) tau) :
    AuxTerm Symbol arity ((A ++ B) ++ Gamma) tau :=
  castContext (List.append_assoc A B Gamma).symm
    (substitute
      (castContext (by simp only [List.append_assoc,List.cons_append])
        (substitute
          (castContext (by simp only [List.append_assoc,List.cons_append]) q)
          (prefixErasure (A ++ alpha :: B) Gamma beta)))
      (prefixErasure A (B ++ Gamma) alpha))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletion
