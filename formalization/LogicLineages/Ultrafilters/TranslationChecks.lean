module
public import LogicLineages.Ultrafilters.Translation
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.Ultrafilters.StatementChecks

theorem fixed_coordinate_image_dichotomy : Targets.CoordinateImageDichotomy :=
  coordinate_image_dichotomy

end LogicLineages.Ultrafilters.StatementChecks

#audit_namespace LogicLineages.Ultrafilters
