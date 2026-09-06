import LRATCatcher.Cover
import LRATCatcher.K28K25DOFlatIcnf0

namespace LRATCatcher.Comparator.K28K25DO
/-- The flat cover (534 leaves), as iCNF text. -/
def flatIcnf : String := icnf0
/-- The cube list: `parseICnf` (Cover.lean) applied to the embedded text. -/
def cubes : List LRATCatcher.Cube := LRATCatcher.parseICnf flatIcnf
end LRATCatcher.Comparator.K28K25DO
