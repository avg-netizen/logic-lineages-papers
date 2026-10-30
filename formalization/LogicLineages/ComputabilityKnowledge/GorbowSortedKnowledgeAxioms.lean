module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanTruth

@[expose] public section
/-! Literal Figure 1 non-triviality, K1-K2 and UKK, and Figure 3 veracity.
Reflection and Base are deliberately absent; positive-stage UKK is not
stage-zero closure for an arbitrary initial extension. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedKnowledgeAxioms
open GorbowSyntax GorbowBooleanTruth

def nontriviality : Sentence := .ex (.agent (.var 0))

def bridge : Sentence := .all (.imp (sentenceGuard (.var 0))
  (biconditional (.knowledgeAll (.var 0))
    (.all (.imp (.agent (.var 0)) (.knowledge (.var 0) (.var 1))))))

-- Outermost a, then phi, then psi; the innermost context is [psi,phi,a].
def distribution : Sentence := .all (.imp (.agent (.var 0))
  (.all (.imp (sentenceGuard (.var 0))
    (.all (.imp (sentenceGuard (.var 0))
      (.imp (.conj (.knowledge (.var 2) (.var 1))
        (.knowledge (.var 2) (binaryCodeTerm 0 (.var 1) (.var 0))))
        (.knowledge (.var 2) (.var 0))))))))

def veracity : Sentence := .all (.imp (.agent (.var 0))
  (.all (.imp (sentenceGuard (.var 0))
    (.imp (.knowledge (.var 1) (.var 0)) (.truth (.var 0))))))
end LogicLineages.ComputabilityKnowledge.GorbowSortedKnowledgeAxioms
