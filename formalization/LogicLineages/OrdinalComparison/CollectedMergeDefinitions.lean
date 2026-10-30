module
public import LogicLineages.OrdinalComparison.CollectedPositiveDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Exact sorted dictionary insertion by structural tag code. Zero is omitted;
for positive source coefficients an equal tag adds its coefficient. -/
def collectedTagInsert (rho : NONote) (A : CollectedPositiveNF) (a : Nat) :
    CollectedPositiveTags → CollectedPositiveTags
  | .nil => if a=0 then .nil else .cons rho A a .nil
  | .cons sigma B b rest =>
    if a=0 then .cons sigma B b rest
    else if collectedTagKey rho A < collectedTagKey sigma B then
      .cons rho A a (.cons sigma B b rest)
    else if collectedTagKey rho A=collectedTagKey sigma B then
      .cons sigma B (a+b) rest
    else .cons sigma B b (collectedTagInsert rho A a rest)

def collectedTagsMerge : CollectedPositiveTags → CollectedPositiveTags → CollectedPositiveTags
  | .nil, right => right
  | .cons rho A a rest, right => collectedTagInsert rho A a (collectedTagsMerge rest right)

def collectedPositiveAdd : CollectedPositiveNF → CollectedPositiveNF → CollectedPositiveNF
  | .mk c b tags, .mk d e rest => .mk (c+d) (b+e) (collectedTagsMerge tags rest)

end LogicLineages.OrdinalComparison
