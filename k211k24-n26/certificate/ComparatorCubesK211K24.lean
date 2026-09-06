import LRATCatcher.Cover
import LRATCatcher.K211K24FlatIcnf0

namespace LRATCatcher.Comparator.K211K24
/-- The flat cover (10017 leaves), as iCNF text. -/
def flatIcnf : String := icnf0
/-- The cube list: `parseICnf` (Cover.lean) applied to the embedded text. -/
def cubes : List LRATCatcher.Cube := LRATCatcher.parseICnf flatIcnf
end LRATCatcher.Comparator.K211K24
